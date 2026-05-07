FROM docker.io/rust:1.94-trixie

USER root

RUN apt-get update \
    && apt-get install -y \
    clang \
    sudo \
    gcc-arm-none-eabi \
    gdb-multiarch \
    libnewlib-dev \
    python3-pip \
    && rm -rf /var/lib/apt/lists/*

RUN rustup component add llvm-tools rustfmt \
    && rustup target add thumbv8m.main-none-eabihf \
    && cargo install flip-link cargo-binstall && cargo binstall probe-rs-tools --no-confirm

