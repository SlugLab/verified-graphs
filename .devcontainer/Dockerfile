FROM ubuntu:24.04

ARG USERNAME=dev
SHELL ["/bin/bash", "-c"]

# The Verus version should match the project's Rust toolchain.
ARG VERUS_VER=release/rolling/0.2025.12.18.10ea71c
ARG VERUS_VER_Z3=z3-4.12.5

ARG DEBIAN_FRONTEND=noninteractive

# Base apt packages.
RUN apt-get update && apt-get install -y \
    build-essential \
    ca-certificates \
    cmake \
    curl \
    git \
    pkg-config \
    python3 \
    python3-venv \
    sudo \
    vim \
    make \
    && rm -rf /var/lib/apt/lists/*

# Add non-root user.
RUN useradd -m -s /bin/bash "${USERNAME}" && echo "${USERNAME} ALL=(ALL) NOPASSWD:ALL" > "/etc/sudoers.d/${USERNAME}"

# Build and install Z3 from source as root.
WORKDIR /tmp
RUN git clone --branch "${VERUS_VER_Z3}" --depth 1 https://github.com/Z3Prover/z3.git && \
    cd z3 && \
    python3 scripts/mk_make.py --prefix=/usr/local && \
    cd build && \
    make -j"$(nproc)" && \
    make install && \
    cd /tmp && \
    rm -rf /tmp/z3

USER ${USERNAME}
ENV HOME=/home/${USERNAME}
ENV PATH="${HOME}/.cargo/bin:${PATH}"

# Install Rust toolchain.
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --profile minimal && \
    rustup component add rustfmt clippy

# Install uv.
RUN curl -LsSf https://astral.sh/uv/install.sh | sh

# Build Verus.
ENV VERUS_SRC=${HOME}/verus
RUN git clone --branch "${VERUS_VER}" --depth 1 https://github.com/verus-lang/verus.git "${VERUS_SRC}" && \
    cd "${VERUS_SRC}/source" && \
    source ../tools/activate && \
    ln -sf $(which z3) ./z3 && \
    vargo build --release
ENV PATH="${VERUS_SRC}/source/target-verus/release:${PATH}"

# Additional non-essential packages.
RUN sudo apt-get update && sudo apt-get install -y \
    tmux \
    neovim \
    zsh \
    && sudo rm -rf /var/lib/apt/lists/*

ENV LANG C.UTF-8
ENV LC_ALL C.UTF-8

WORKDIR ${HOME}
