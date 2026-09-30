FROM mcr.microsoft.com/devcontainers/base:ubuntu24.04

USER vscode
ENV PATH="/home/vscode/.elan/bin:${PATH}"

COPY --chown=vscode:vscode lean-toolchain /tmp/lean-toolchain
RUN curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh \
    && sh /tmp/elan-init.sh -y --default-toolchain none \
    && elan toolchain install "$(cat /tmp/lean-toolchain)"
