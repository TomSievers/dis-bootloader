FROM docker.io/rust:1.89-bookworm

USER root

RUN apt-get update \
    && apt-get install -y \
    clang \
    sudo \
    gcc-arm-none-eabi \
    gdb-arm-none-eabi \
    libnewlib-dev \
    python3-pip \
    && rm -rf /var/lib/apt/lists/*

RUN rustup component add llvm-tools rustfmt \
    && rustup target add thumbv8m.main-none-eabihf \
    && cargo install flip-link cargo-binstall \
    && cargo binstall probe-rs-tools -y --version 0.27.0