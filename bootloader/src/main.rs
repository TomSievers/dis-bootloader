#![doc = include_str!("../../README.md")]
#![no_main]
#![no_std]
#![warn(missing_docs)]

use panic_persist as _;

use crate::flash::Flash;
use core::mem::MaybeUninit;
use cortex_m::peripheral::{sau::Ctrl, SAU, SCB};

use embassy_nrf::pac::{self, spu::vals::Present, NVMC, SPU};

use panic_persist::get_panic_message_bytes;

use rtt_target::{rprintln, rtt_init_print};

use shared::{
    flash_addresses::{
        bootloader_flash_page_range, bootloader_flash_range, bootloader_scratch_page_range,
        bootloader_scratch_range, bootloader_state_page_range, bootloader_state_range,
        program_slot_a_page_range, program_slot_a_range, program_slot_b_page_range,
        program_slot_b_range, PAGE_SIZE,
    },
    state::{BootloaderGoal, BootloaderState, PageState},
};

mod flash;

/// A counter that keeps track of how many panics there have been. It keeps its value across resets.
#[link_section = ".uninit"]
static mut PANIC_COUNTS: MaybeUninit<u32> = MaybeUninit::uninit();

/// A print macro that takes either UART or RTT to print
#[macro_export]
macro_rules! println {
    ($($arg:tt)*) => {
        rprintln!($($arg)*);
    };
}

mod consts {
    pub const UICR_APPROTECT: *mut u32 = 0x00FF8000 as *mut u32;
    pub const UICR_HFXOSRC: *mut u32 = 0x00FF801C as *mut u32;
    pub const UICR_HFXOCNT: *mut u32 = 0x00FF8020 as *mut u32;
    pub const UICR_SECUREAPPROTECT: *mut u32 = 0x00FF802C as *mut u32;
    pub const APPROTECT_ENABLED: u32 = 0x0000_0000;
    #[cfg(feature = "nrf9120")]
    pub const APPROTECT_DISABLED: u32 = 0x50FA50FA;
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum WriteResult {
    /// Word was written successfully, needs reset.
    Written,
    /// Word was already set to the value we wanted to write, nothing was done.
    Noop,
    /// Word is already set to something else, we couldn't write the desired value.
    Failed,
}

unsafe fn uicr_write(address: *mut u32, value: u32) -> WriteResult {
    uicr_write_masked(address, value, 0xFFFF_FFFF)
}

unsafe fn uicr_write_masked(address: *mut u32, value: u32, mask: u32) -> WriteResult {
    let curr_val = address.read_volatile();
    if curr_val & mask == value & mask {
        return WriteResult::Noop;
    }

    // We can only change `1` bits to `0` bits.
    if curr_val & value & mask != value & mask {
        return WriteResult::Failed;
    }

    // Nrf9151 errata 7, need to disable interrups + use DSB https://docs.nordicsemi.com/bundle/errata_nRF9151_Rev2/page/ERR/nRF9151/Rev2/latest/anomaly_151_7.html
    cortex_m::interrupt::free(|_cs| {
        let nvmc = pac::NVMC;

        nvmc.config()
            .write(|w| w.set_wen(pac::nvmc::vals::Wen::WEN));
        while !nvmc.ready().read().ready() {}
        address.write_volatile(value | !mask);
        cortex_m::asm::dsb();
        while !nvmc.ready().read().ready() {}
        nvmc.config().write(|_| {});
        while !nvmc.ready().read().ready() {}
    });

    WriteResult::Written
}

#[cortex_m_rt::entry]
unsafe fn run_main() -> ! {
    let core_peripherals = cortex_m::Peripherals::take().unwrap();

    let mut needs_reset = false;

    let uicr = pac::UICR_S;
    let hfxocnt = uicr.hfxocnt().read().hfxocnt().to_bits();
    let hfxosrc = uicr.hfxosrc().read().hfxosrc().to_bits();

    if hfxosrc == 1 {
        unsafe {
            let _ = uicr_write(consts::UICR_HFXOSRC, 0);
        }
        needs_reset = true;
    }

    if hfxocnt == 255 {
        unsafe {
            let _ = uicr_write(consts::UICR_HFXOCNT, 32);
        }
        needs_reset = true;
    }

    #[cfg(feature = "nrf9120")]
    unsafe {
        use embassy_nrf::pac;

        let p = pac::APPROTECT_S;

        let res = uicr_write(consts::UICR_APPROTECT, consts::APPROTECT_DISABLED);
        needs_reset |= res == WriteResult::Written;
        p.approtect().disable().write(|w| {
            w.set_disable(pac::approtect::vals::ApprotectDisableDisable::SW_UNPROTECTED)
        });

        let res = uicr_write(consts::UICR_SECUREAPPROTECT, consts::APPROTECT_DISABLED);
        needs_reset |= res == WriteResult::Written;
        p.secureapprotect().disable().write(|w| {
            w.set_disable(pac::approtect::vals::SecureapprotectDisableDisable::SW_UNPROTECTED)
        });
    }

    if needs_reset {
        cortex_m::peripheral::SCB::sys_reset();
    }

    // Embassy doesn't give us a pac instance of the NVMC, so we need to make a reference ourselves
    let mut flash = Flash { registers: &NVMC };

    rtt_init_print!();

    println!("Dis-Bootloader starting up...");

    // Get how many panics we've gotten
    let panics = unsafe { PANIC_COUNTS.assume_init_mut() };
    if *panics > 10 {
        // Probably random garbage from ram, so we've probably just booted
        *panics = 0;
    }

    // Check if there was a panic message, if so, send to UART
    if let Some(msg) = get_panic_message_bytes() {
        println!("Booted up from a panic:");
        let msg = unsafe { core::str::from_utf8_unchecked(msg) };
        println!("{}", msg);
        *panics += 1;
    }

    println!("Panic count {}", panics);

    // If there are too many panics, let's just sleep and potentially save the flash memory
    if *panics > 10 {
        println!("Too many panics, going to sleep and resetting");
        *panics = 0;

        // When on the nrf9120 we need to make sure that the constant latency mode enabled when entering system on idle.
        // See: https://docs.nordicsemi.com/bundle/errata_nRF9151_Rev1/page/ERR/nRF9151/Rev1/latest/anomaly_151_36.html#anomaly_151_36
        #[cfg(feature = "nrf9120")]
        {
            pac::POWER.tasks_constlat().write(|w| *w = 1);
            cortex_m::asm::dsb();
        }

        cortex_m::asm::wfi();
        cortex_m::peripheral::SCB::sys_reset();
    }

    // Print the memory regions we're using, just for convenience
    println!("\nDefined memory regions:");
    println!(
        "\tbootloader flash:   {:08X?} ({:03?})",
        bootloader_flash_range(),
        bootloader_flash_page_range()
    );
    println!(
        "\tbootloader scratch: {:08X?} ({:03?})",
        bootloader_scratch_range(),
        bootloader_scratch_page_range()
    );
    println!(
        "\tbootloader state:   {:08X?} ({:03?})",
        bootloader_state_range(),
        bootloader_state_page_range()
    );
    println!(
        "\tprogram slot a:     {:08X?} ({:03?})",
        program_slot_a_range(),
        program_slot_a_page_range()
    );
    println!(
        "\tprogram slot b:     {:08X?} ({:03?})",
        program_slot_b_range(),
        program_slot_b_page_range()
    );

    // Let's check what we need to do by loading the state
    let mut state = BootloaderState::load(&flash);

    let sau = core_peripherals.SAU;
    let scb = core_peripherals.SCB;

    // The state must be valid or we will just jump to the application
    if !state.is_valid() {
        println!("State is invalid, jumping to application");
        jump_to_application(scb, sau);
    }

    let goal = state.goal();
    println!("Goal: {:?}", goal);

    match goal {
        BootloaderGoal::JumpToApplication => {
            jump_to_application(scb, sau);
        }
        BootloaderGoal::StartSwap => {
            state.prepare_swap(false, &mut flash); // TODO: think about reset here
            perform_swap(false, &mut state, &mut flash);
            jump_to_application(scb, sau);
        }
        BootloaderGoal::FinishSwap => {
            perform_swap(false, &mut state, &mut flash);
            jump_to_application(scb, sau);
        }
        BootloaderGoal::StartTestSwap => {
            state.prepare_swap(true, &mut flash);
            perform_swap(true, &mut state, &mut flash);
            jump_to_application(scb, sau);
        }
        BootloaderGoal::FinishTestSwap => {
            perform_swap(true, &mut state, &mut flash);
            jump_to_application(scb, sau);
        }
    }
}

/// Actually performs the swapping procedure.
///
/// If the state has been prepared for a swap, all pages will be swapped.
/// If not, then it will resume a previous swap.
fn perform_swap(test_swap: bool, state: &mut BootloaderState, flash: &mut impl shared::Flash) {
    // Gather info about our memory layout
    let total_program_pages = program_slot_a_page_range().len() as u32;
    let total_scratch_pages = bootloader_scratch_page_range().len() as u32;

    println!("total_program_pages: {}", total_program_pages);
    println!("total_scratch_pages: {}", total_scratch_pages);

    // We're doing a round-robin for scratch page usage, so we need to keep track of the used index
    let mut scratch_page_index = 0;

    // We need to swap every page
    for page in 0..total_program_pages {
        // Get the addresses of the A and B page slot
        let slot_a_page = program_slot_a_page_range().start + page;
        let slot_a_address = slot_a_page * PAGE_SIZE;
        let slot_b_page = program_slot_b_page_range().start + page;
        let slot_b_address = slot_b_page * PAGE_SIZE;

        // We run a small statemachine that needs to continue until the page is swapped.
        // If we resume a swap due to a reset, then it is possible that a lot of pages have already been swapped
        while !state.get_page_state(page).is_swapped() {
            println!("Swapping page {}: {:?}", page, state.get_page_state(page));
            // Depending on the state, we need to swap certain pages
            match state.get_page_state(page) {
                PageState::Original => {
                    // We need to copy the A page to a scratch page

                    // Decide which scratch page to use
                    let scratch_page = bootloader_scratch_page_range().start + scratch_page_index;
                    let scratch_address = scratch_page * PAGE_SIZE;

                    println!(
                        "Moving page @{:#010X} to page {:#010X}",
                        slot_a_address, scratch_address
                    );

                    // Erase the scratch area
                    flash.erase_page(scratch_address);
                    // Program the data from slot A into the scratch slot
                    flash.program_page(scratch_address, unsafe {
                        core::slice::from_raw_parts(
                            slot_a_address as *const u32,
                            PAGE_SIZE as usize / core::mem::size_of::<u32>(),
                        )
                    });
                    // Update the state
                    state.set_page_state(page, PageState::InScratch { scratch_page });
                    state.burn_store(flash);
                }
                PageState::InScratch { scratch_page } => {
                    // We need to copy the B page to the A slot

                    println!(
                        "Moving page @{:#010X} to page {:#010X}",
                        slot_b_address, slot_a_address
                    );

                    // Erase the A page
                    flash.erase_page(slot_a_address);
                    // Program the data from slot B into the A slot
                    flash.program_page(slot_a_address, unsafe {
                        core::slice::from_raw_parts(
                            slot_b_address as *const u32,
                            PAGE_SIZE as usize / core::mem::size_of::<u32>(),
                        )
                    });
                    // Update the state
                    state.set_page_state(page, PageState::InScratchOverwritten { scratch_page });
                    state.burn_store(flash);
                }
                PageState::InScratchOverwritten { scratch_page } => {
                    // We need to copy the scratch page to the B slot

                    let scratch_address = scratch_page * PAGE_SIZE;

                    println!(
                        "Moving page @{:#010X} to page {:#010X}",
                        scratch_address, slot_b_address
                    );

                    // Erase the B page
                    flash.erase_page(slot_b_address);
                    // Program the data from the scratch slot into the B slot
                    flash.program_page(slot_b_address, unsafe {
                        core::slice::from_raw_parts(
                            scratch_address as *const u32,
                            PAGE_SIZE as usize / core::mem::size_of::<u32>(),
                        )
                    });
                    // Update the state
                    state.set_page_state(page, PageState::Swapped);

                    state.burn_store(flash);
                }
                PageState::Swapped => {
                    // We're done and shouldn't be able to get here
                    unreachable!()
                }
            }
        }

        // Go to the next scratch page or start over if we were on the last one
        scratch_page_index = (scratch_page_index + 1) % total_scratch_pages;
    }

    // We're done, so we should change the state
    if test_swap {
        state.set_goal(BootloaderGoal::StartSwap);
    } else {
        state.set_goal(BootloaderGoal::JumpToApplication);
    }

    // We've changed the goal, so we need to store that
    state.store(flash);
}

/// Jump to the application if the application vector table can be found
fn jump_to_application(scb: SCB, sau: SAU) -> ! {
    // The application may not be stationed at the start of its slot.
    // We need to search for it first.
    // We will bootload to the first non-erased & non-padding (0xFFFF_FFFF, 0x0000_0000) word if the word after it could be a pointer to a reset vector inside the program_slot_a_range.
    // (The first word of the vector table is the initial stack pointer)
    let mut application_address = None;

    let mut found_init_stack_pointer = false;

    for possible_address in program_slot_a_range().step_by(4) {
        // We can read this address safely because it will always be in flash
        let address_value = unsafe { (possible_address as *const u32).read_volatile() };

        match address_value {
            0xFFFF_FFFF => continue,
            0x0000_0000 => continue,
            _ if (0x2000_0000..0x2004_0000).contains(&address_value)
                && !found_init_stack_pointer =>
            {
                application_address = Some(possible_address);
                found_init_stack_pointer = true;
            }
            _ if program_slot_a_range().contains(&address_value) && found_init_stack_pointer => {
                break;
            }
            _ => {
                application_address = None;
                break;
            }
        }
    }

    match application_address {
        Some(application_address) => {
            println!("Jumping to {:#08X}", application_address);

            unsafe {
                let spu = SPU;

                // Leave the first 64KiB as secure and make everything else non secure
                for region in 2..32 {
                    spu.flashregion(region).perm().write(|w| {
                        w.set_execute(true);
                        w.set_write(true);
                        w.set_read(true);
                        w.set_secattr(false);
                        w.set_lock(false);
                    })
                }

                // Leave the first 64KiB as secure and make everything else non secure
                for region in 8..32 {
                    spu.ramregion(region).perm().write(|w| {
                        w.set_execute(true);
                        w.set_write(true);
                        w.set_read(true);
                        w.set_secattr(false);
                        w.set_lock(false);
                    })
                }

                // Use the NVIC ITNS register to target interrupts as non secure
                let nvic_itns = 0xE000E380 as *mut u32;

                // Make all peripherals non secure if present.
                for i in 0..67 {
                    let periph = spu.periphid(i);
                    if periph.perm().read().present() == Present::IS_PRESENT {
                        periph.perm().write(|w| w.set_secattr(true));
                        let mut val = core::ptr::read_volatile(nvic_itns.offset((i / 32) as isize));
                        val |= 1 << (i % 32);
                        core::ptr::write_volatile(nvic_itns.offset((i / 32) as isize), val);
                    }
                }

                // Allow non secure access for EXT DOMAIN
                spu.extdomain(0).perm().write(|w| w.set_lock(false));

                // Mark all pins non secure.
                spu.gpioport(0).perm().write(|w| w.0 = 0);

                // Make all DPPI channels non secure.
                spu.dppi(0).perm().write(|w| w.0 = 0);

                // Configure the SAU to ALLNS and disabled, to allow the SPU to take over.
                sau.ctrl.write(Ctrl(0x02));

                let aircr = scb.aircr.read() & 0xFFFF;
                // Set BFHFNMINS to 1, making fault and nmi exceptions non secure
                scb.aircr.write(aircr | 0x05FA_0000 | (1 << 13));
                // Target systick non secure
                scb.icsr.modify(|w| w | (1 << 24));

                bootload_ns(application_address as *const u32);
            }
        }
        None => panic!("Could not find a reset vector in the firmware"),
    }
}

unsafe fn bootload_ns(vector_table: *const u32) -> ! {
    let msp = core::ptr::read_volatile(vector_table);
    let rv = core::ptr::read_volatile(vector_table.offset(1));

    // Write the NS VTOR.
    let vtor_ns = 0xE002ED08 as *mut u32;
    core::ptr::write_volatile(vtor_ns, vector_table as u32);

    // Allow non secure access to all possible coprocessors
    let scb_nsacr = 0xE000ED8C as *mut u32;
    core::ptr::write_volatile(scb_nsacr, 0xCFFu32);

    __bootload_asm(msp as *const u32, rv as *const u32);
}

unsafe fn __bootload_asm(msp: *const u32, rv: *const u32) -> ! {
    // Adapted from the cortex-m boostrap implementation to boot a NS application
    core::arch::asm!(
        "mrs {tmp}, CONTROL_NS",
        "bics {tmp}, {spsel}",
        "msr CONTROL_NS, {tmp}",
        "isb",
        "msr MSP_NS, {msp}",
        "movs {tmp}, #0",
        "msr PSP_NS, {tmp}",
        "movs {tmp}, #1",
        "bics {rv}, {tmp}",
        "dsb sy",
        "isb sy",
        "bxns {rv}",
        // `out(reg) _` is not permitted in a `noreturn` asm! call,
        // so instead use `in(reg) 0` and don't restore it afterwards.
        tmp = in(reg) 0,
        spsel = in(reg) 2,
        msp = in(reg) msp,
        rv = in(reg) rv,
        options(noreturn, nomem, nostack),
    )
}

#[cortex_m_rt::exception]
unsafe fn HardFault(frame: &cortex_m_rt::ExceptionFrame) -> ! {
    // Just panic because we probably want to reboot
    panic!("Hardfault: {:?}", frame);
}
