# Create a docker image for running the benchmarks.
# Build:
# > docker build -t <mytag> .
#
# To Run:
# > docker run -it <mytag>
# or
# > docker run -v <local-dir> -it <mytag>

FROM ubuntu:22.04
RUN apt-get update
RUN apt-get install -y --no-install-recommends ca-certificates
RUN apt-get install -y --no-install-recommends cmake make
RUN apt-get install -y --no-install-recommends git
RUN apt-get install -y --no-install-recommends gcc libc-dev
RUN apt-get install -y --no-install-recommends curl xz-utils gnupg netbase zlib1g-dev
RUN apt-get install -y --no-install-recommends build-essential tar
RUN rm -rf /var/lib/apt/lists/*

# Swift
WORKDIR /build
RUN curl -O https://download.swift.org/swift-5.8.1-release/ubuntu2204/swift-5.8.1-RELEASE/swift-5.8.1-RELEASE-ubuntu22.04.tar.gz
RUN tar -xzf  swift-5.8.1-RELEASE-ubuntu22.04.tar.gz
WORKDIR /build/swift-5.8.1-RELEASE-ubuntu22.04/usr
RUN mkdir /opt/swift
RUN cp -r * /opt/swift
RUN rm -rf /build/swift-5.8.1-RELEASE-ubuntu22.04
RUN rm /build/swift-5.8.1-RELEASE-ubuntu22.04.tar.gz

# Java 
WORKDIR /build
RUN apt-get update
RUN apt-get install -y --no-install-recommends software-properties-common
RUN add-apt-repository ppa:linuxuprising/java
RUN echo debconf shared/accepted-oracle-license-v1-3 select true | debconf-set-selections
RUN echo debconf shared/accepted-oracle-license-v1-3 seen true | debconf-set-selections
RUN apt-get install -y --no-install-recommends oracle-java17-installer
RUN apt-get install -y --no-install-recommends oracle-java17-set-default
RUN apt-get install -y --no-install-recommends libedit2 libz3-dev
RUN apt-get install -y --no-install-recommends time

# Haskell
WORKDIR /build
RUN apt-get install -y --no-install-recommends ghc cabal-install
RUN cabal update
RUN cabal install parallel

# OCaml (multicore)
WORKDIR /build
RUN apt-get install -y --no-install-recommends opam
RUN opam init -y --disable-sandboxing 
RUN opam update -y
RUN opam switch -y create 5.0.0

RUN wget https://github.com/microsoft/vcpkg/archive/refs/tags/2023.06.20.tar.gz
RUN tar -xzf 2023.06.20.tar.gz
RUN mv vcpkg-2023.06.20 ~/vcpkg

# Stack
WORKDIR /build
RUN curl -sSL https://get.haskellstack.org/ | sh
COPY . /build/koka
WORKDIR /build/koka
RUN stack setup
RUN stack build

RUN apt-get install -y --no-install-recommends npm

SHELL ["/bin/bash", "-c"]
RUN echo "ulimit -s unlimited" >> ~/.bashrc 
RUN opam env >> ~/.bashrc
