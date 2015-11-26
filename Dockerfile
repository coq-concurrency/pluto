FROM ubuntu:14.04
MAINTAINER Guillaume Claret

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y gcc make git
RUN apt-get install -y curl m4 ruby

# OCaml
WORKDIR /root
RUN curl -L https://github.com/ocaml/ocaml/archive/4.02.3.tar.gz |tar -xz
WORKDIR /root/ocaml-4.02.3
RUN ./configure && make world.opt && make install

# Camlp4
WORKDIR /root
RUN curl -L https://github.com/ocaml/camlp4/archive/4.02+6.tar.gz |tar -xz
WORKDIR /root/camlp4-4.02-6
RUN ./configure && make all && make install

# OPAM
WORKDIR /root
RUN curl -L https://github.com/ocaml/opam/archive/1.2.2.tar.gz |tar -xz
WORKDIR opam-1.2.2
RUN ./configure && make lib-ext && make && make install

# Tools
RUN apt-get install -y inotify-tools aspcud unzip

# Initialize OPAM
RUN opam init
ENV OPAMJOBS 4

# Coq
RUN opam install -y coq

# Coq repository
RUN opam repo add coq-released https://coq.inria.fr/opam/released

# Dependencies
RUN opam install -y coq-error-handlers coq-function-ninjas coq-iterable coq-list-string coq-moment
RUN opam install -y coq-concurrency-proxy coq-concurrency-system

# Build
ADD . /root/pluto
WORKDIR /root/pluto
RUN eval `opam config env`; ./configure.sh && make -j
WORKDIR extraction
RUN eval `opam config env`; make

# Run the server
EXPOSE 80
CMD eval `opam config env`; ./pluto.native 80 ../html
