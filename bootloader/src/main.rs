#![doc = include_str!("../../README.md")]
#![no_main]
#![no_std]
#![feature(type_alias_impl_trait)]
#![warn(missing_docs)]

use crate::flash::Flash;
use core::mem::MaybeUninit;
use cortex_m::peripheral::{sau::Ctrl, SAU};

use embassy_nrf::pac::SPU;
#[cfg(feature = "uart-log")]
use embassy_nrf::{
    interrupt,
    peripherals::UARTETWISPI0,
    uarte::{self, Uarte},
};
use panic_persist::get_panic_message_bytes;
#[cfg(not(feature = "uart-log"))]
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

#[cfg(feature = "uart-log")]
type Uart = Uarte<'static, UARTETWISPI0>;

/// A counter that keeps track of how many panics there have been. It keeps its value across resets.
#[link_section = ".uninit"]
static mut PANIC_COUNTS: MaybeUninit<u32> = MaybeUninit::uninit();

#[embassy_executor::main]
async fn main(_spawner: embassy_executor::Spawner) {
    let device_peripherals = embassy_nrf::init(Default::default());
    let core_peripherals = cortex_m::Peripherals::take().unwrap();
    // Rust analyzer doesn't like the embassy macro, so as a hack, just immediately go to another function without it
    run_main(device_peripherals, core_peripherals).await;
}

/// A print macro that takes either UART or RTT to print
#[macro_export]
macro_rules! println {
    ($($arg:tt)*) => {
        #[cfg(feature = "uart-log")]
        uprintln!($($arg)*);
        #[cfg(not(feature = "uart-log"))]
        rprintln!($($arg)*);
    };
}

/// A print macro that takes the uart and then the print expression like println!.
#[macro_export]
macro_rules! uprintln {
    ($($arg:tt)*) => {
        {
            use core::fmt::Write as _;
            let mut str = arrayvec::ArrayString::<1024>::new();
            match writeln!(str, $($arg)*) {
                Ok(_) => {
                    UART.as_mut().unwrap().write(str.as_bytes()).await.unwrap();
                },
                Err(_) => UART.as_mut().unwrap().write("Error: failed to print string, too long".as_bytes()).await.unwrap(),
            };
        }
    };
}

async fn run_main(
    device_peripherals: embassy_nrf::Peripherals,
    core_peripherals: cortex_m::Peripherals,
) {
    // Embassy doesn't give us a pac instance of the NVMC, so we need to make a reference ourselves
    let mut flash = Flash {
        registers: unsafe { &*embassy_nrf::pac::NVMC::PTR },
    };

    #[cfg(feature = "uart-log")]
    {
        let mut config = uarte::Config::default();
        config.parity = uarte::Parity::EXCLUDED;
        config.baudrate = uarte::Baudrate::BAUD115200;

        let irq = interrupt::take!(UARTE0_SPIM0_SPIS0_TWIM0_TWIS0);

        #[cfg(feature = "feather")]
        let (uart_rx_pin, uart_tx_pin) = (device_peripherals.P0_05, device_peripherals.P0_06);
        #[cfg(feature = "logistics")]
        let (uart_rx_pin, uart_tx_pin) = (device_peripherals.P0_28, device_peripherals.P0_29);
        #[cfg(feature = "mobility")]
        let (uart_rx_pin, uart_tx_pin) = (device_peripherals.P0_28, device_peripherals.P0_29);
        #[cfg(feature = "turing")]
        let (uart_rx_pin, uart_tx_pin) = (device_peripherals.P0_30, device_peripherals.P0_19);
        #[cfg(feature = "actinius_icarus")]
        let (uart_rx_pin, uart_tx_pin) = (device_peripherals.P0_06, device_peripherals.P0_09);

        UART = Some(uarte::Uarte::new(
            device_peripherals.UARTETWISPI0,
            irq,
            uart_rx_pin,
            uart_tx_pin,
            config,
        ));
    }

    #[cfg(not(feature = "uart-log"))]
    rtt_init_print!();

    // Configure the uart

    // Show a sign of life and print the version
    println!(
        "\n\n--== == == == == == == == == == == == == == ==--\nStarting bootloader version `{}` with git hash `{}`",
        env!("CP_CARGO"),
        env!("CP_GIT")
    );

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

    println!("There have been {} panics so far.", panics);

    // If there are too many panics, let's just sleep and potentially save the flash memory
    if *panics > 10 {
        println!( "There have been too many panics. Bootloader will try to save the flash by going to sleep. The device can be woken up by sending a single byte over serial. The panics counter will then be reset to 0 so you can see all the output again");
        *panics = 0;
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

    // The state must be valid or we will just jump to the application
    if !state.is_valid() {
        println!("State is invalid, jumping to application");
        jump_to_application(sau).await;
    }

    let goal = state.goal();
    println!("Goal: {:?}", goal);

    match goal {
        BootloaderGoal::JumpToApplication => {
            jump_to_application(sau).await;
        }
        BootloaderGoal::StartSwap => {
            state.prepare_swap(false, &mut flash); // TODO: think about reset here
            perform_swap(false, &mut state, &mut flash).await;
            jump_to_application(sau).await;
        }
        BootloaderGoal::FinishSwap => {
            perform_swap(false, &mut state, &mut flash).await;
            jump_to_application(sau).await;
        }
        BootloaderGoal::StartTestSwap => {
            state.prepare_swap(true, &mut flash);
            perform_swap(true, &mut state, &mut flash).await;
            jump_to_application(sau).await;
        }
        BootloaderGoal::FinishTestSwap => {
            perform_swap(true, &mut state, &mut flash).await;
            jump_to_application(sau).await;
        }
    }

    loop {}
}

/// Actually performs the swapping procedure.
///
/// If the state has been prepared for a swap, all pages will be swapped.
/// If not, then it will resume a previous swap.
async fn perform_swap(
    test_swap: bool,
    state: &mut BootloaderState,
    flash: &mut impl shared::Flash,
) {
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
async fn jump_to_application(sau: SAU) -> ! {
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

            #[cfg(feautre = "uart-log")]
            {
                // We need to disable all used peripherals
                drop(UART.take().unwrap());
            }

            unsafe {
                let spu = core::mem::transmute::<_, SPU>(());

                // Leave the first 64KiB as secure and make everything else non secure
                for region in spu.flashregion.iter().skip(2) {
                    region.perm.write(|w| {
                        w.secattr()
                            .non_secure()
                            .read()
                            .enable()
                            .write()
                            .enable()
                            .execute()
                            .enable()
                    });
                }

                // Leave the first 64KiB as secure and make everything else non secure
                for region in spu.ramregion.iter().skip(8) {
                    region.perm.write(|w| {
                        w.secattr()
                            .non_secure()
                            .execute()
                            .enable()
                            .read()
                            .enable()
                            .write()
                            .enable()
                    });
                }

                // Make all peripherals non secure if present.
                for periph in &spu.periphid {
                    if periph.perm.read().present().is_is_present() {
                        periph.perm.write(|w| w.secattr().non_secure())
                    }
                }

                // Make all pins non secure
                for pin in &spu.gpioport {
                    pin.perm.write(|w| w.bits(0x00));
                }

                // Make all dppi non secure.
                for dppi in &spu.dppi {
                    dppi.perm.write(|w| w.bits(0));
                }

                // Configure the SAU to ALLNS and disabled, to allow the SPU to take over.
                sau.ctrl.write(Ctrl(0x02));

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
