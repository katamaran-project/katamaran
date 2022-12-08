FROM gitpod/workspace-full
LABEL maintainer="steven.keuchel@gmail.com"

ARG OCAML_VERSION=4.14.0
ARG COQ_VERSION=8.16.1
ARG IRIS_VERSION=3.6.0
ARG EQUATIONS_VERSION=1.3+8.16

# Install system packages
RUN sudo add-apt-repository -y ppa:avsm/ppa \
&& sudo apt-get update -y \
&& sudo apt-get install -y opam rsync aspcud tmux \
&& sudo apt-get clean \
&& sudo rm -fr /var/lib/apt/lists/*

# Install common packages
## Use bare init to work around https://github.com/ocaml/opam/issues/4838
RUN set -x \
&& opam init --auto-setup --yes --disable-sandboxing --bare --dot-profile=~/.bashrc \
&& opam switch -vyj$(nproc) create 4.14.0 --package=ocaml-variants.4.14.0+options,ocaml-option-flambda \
&& opam repo add --all-switches --set-default coq-released https://coq.inria.fr/opam/released \
&& opam install -vyj$(nproc) dune num ocamlfind zarith conf-findutils conf-gmp opam-depext \
&& opam clean -acrs --logs \
&& opam config list && opam list

# Install Coq and coq packages
RUN set -x \
&& opam install -vyj$(nproc) coq=$COQ_VERSION coq-iris=$IRIS_VERSION coq-equations=$EQUATIONS_VERSION \
&& opam clean -acrs --logs \
&& opam config list && opam list
