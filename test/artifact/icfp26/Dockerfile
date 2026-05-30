# Dockerfile for the artifact:
#   "HMCFA: A Precise and Practical Big-Step Control Flow Analysis for Effect Handlers"
#
# Build this image from the root of the koka repository:
#   docker build -t icfp26-hmcfa -f test/artifact/icfp26/Dockerfile .
#
# (Before building, sync the reference benchmark data:
#   rsync -a benchmarks/results/ benchmarks/results-cached/ )
#
# Run interactively:
#   docker run -it icfp26-hmcfa
#
# The working directory inside the container will be /root/koka.
FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update
RUN apt-get install -y --no-install-recommends ca-certificates
RUN apt-get install -y --no-install-recommends git cmake make
RUN apt-get install -y --no-install-recommends clang gcc libc-dev
RUN apt-get install -y --no-install-recommends build-essential pkg-config curl
RUN apt-get install -y --no-install-recommends tar zip unzip xz-utils
RUN apt-get install -y --no-install-recommends libffi-dev libgmp-dev zlib1g-dev pcre2-utils
RUN apt-get install -y --no-install-recommends vim
RUN apt-get install -y --no-install-recommends python3 python3-pip python3-venv
RUN apt-get update

# Install Stack (Haskell build tool)
WORKDIR /root
RUN curl -sSL https://get.haskellstack.org/ | /bin/bash
RUN stack update

# Install vcpkg
RUN git clone https://github.com/microsoft/vcpkg.git
WORKDIR /root/vcpkg
RUN ./bootstrap-vcpkg.sh

# Install elan (Lean version manager)
WORKDIR /root
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:$PATH"

# Copy and build the Koka compiler
WORKDIR /root
COPY . /root/koka

WORKDIR /root/koka
RUN stack build --fast

# Compile the standard libraries
RUN stack exec koka -- util/link-std.kk

# Install Python dependencies for figure generation
RUN pip3 install --break-system-packages matplotlib numpy pandas scipy seaborn

# Build the Lean proof (fetches and compiles mathlib; cached in this Docker layer)
WORKDIR /root/koka/lean
RUN elan toolchain install "$(cat lean-toolchain)"
RUN lake build

# Environment
WORKDIR /root/koka
SHELL ["/bin/bash", "-c"]
CMD ["/bin/bash"]
