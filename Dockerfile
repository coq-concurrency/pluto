FROM ubuntu:14.10
MAINTAINER Guillaume Claret

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y gcc make git
RUN apt-get install -y curl m4 ruby

# OCaml
WORKDIR /root
RUN curl -L https://github.com/ocaml/ocaml/archive/4.02.1.tar.gz |tar -xz
WORKDIR /root/ocaml-4.02.1
RUN ./configure
RUN make world.opt
RUN make install

# Camlp4
WORKDIR /root
RUN curl -L https://github.com/ocaml/camlp4/archive/4.02.1+1.tar.gz |tar -xz
WORKDIR /root/camlp4-4.02.1-1
RUN ./configure
RUN make all
RUN make install

# OPAM
WORKDIR /root
RUN curl -L https://github.com/ocaml/opam/archive/1.2.0.tar.gz |tar -xz
WORKDIR opam-1.2.0
RUN ./configure
RUN make lib-ext
RUN make
RUN make install

# Initialize OPAM
RUN opam init
ENV OPAMJOBS 4

# Coq
RUN opam install -y coq

# Tools
RUN apt-get install -y inotify-tools

# Coq repositories
RUN echo 4
RUN opam repo add coq-stable https://github.com/coq/repo-stable.git
RUN opam repo add coq-unstable https://github.com/coq/repo-unstable.git

# Dependencies
RUN opam install -y coq:error-handlers coq:function-ninjas coq:iterable coq:list-string coq:moment
RUN opam install -y coq:concurrency:proxy coq:concurrency:system

# Build
ADD . /root/pluto
WORKDIR /root/pluto
RUN eval `opam config env`; ./configure.sh && make -j
WORKDIR extraction
RUN eval `opam config env`; make

# Run the server
EXPOSE 80
CMD eval `opam config env`; ./pluto.native 80 ../html
