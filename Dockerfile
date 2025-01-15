# syntax=docker/dockerfile:1.7-labs

FROM --platform=linux/amd64 ocaml/opam:ubuntu-lts-ocaml-5.0

ARG DEBIAN_FRONTEND=noninteractive
USER root
RUN apt-get update -y && apt-get install git python3 clang clang-format autoconf \
    pkg-config libclang-15-dev libclang-cpp15-dev llvm-15-dev zlib1g-dev coq \
    openjdk-21-jdk csvkit -y

# Our sources
WORKDIR /usr/src
COPY --parents KAT_Decompile/frontend/ KAT_Decompile/lib/ KAT_Decompile/ctocfgkat/ KAT_Decompile/dune-project /usr/src/

# opam stuff
WORKDIR /usr/src/KAT_Decompile
RUN opam init --disable-sandboxing
RUN opam install qcheck unionFind clangml FrontC dune calipso
RUN eval $(opam env) && dune build

# coreutils stuff
WORKDIR /usr/src
ADD https://gnu.mirror.constant.com/coreutils/coreutils-9.5.tar.gz coreutils-9.5.tar.gz
RUN tar xvzf coreutils-9.5.tar.gz
RUN rm coreutils-9.5.tar.gz

WORKDIR /usr/src/coreutils-9.5
RUN CC=clang CXX=clang++ FORCE_UNSAFE_CONFIGURE=1 ./configure
RUN make

COPY KAT_Decompile/peakyblinders.py /usr/src
WORKDIR /usr/src
RUN python3 -u peakyblinders.py coreutils-9.5 KAT_Decompile coreutils-9.5-blinded coreutils-9.5-blinded.csv

# Coq stuff
COPY --parents formalization/main.v /usr/src
WORKDIR /usr/src/formalization
RUN coqc main.v

# Ghidra
ADD https://github.com/NationalSecurityAgency/ghidra/releases/download/Ghidra_11.2_build/ghidra_11.2_PUBLIC_20240926.zip /tmp/ghidra.zip
RUN unzip /tmp/ghidra.zip -d /opt
RUN mv /opt/ghidra_11.2_PUBLIC /opt/ghidra
RUN rm /tmp/ghidra.zip
COPY decompile.py /usr/src

# pollard_rho
COPY pollard_rho/pollard_rho.c /usr/src/coreutils-9.5-blinded/src
COPY pollard_rho/pollard_rho-clean.c /usr/src/coreutils-9.5-blinded/src

WORKDIR /usr/src/
ENTRYPOINT ["bash"]
