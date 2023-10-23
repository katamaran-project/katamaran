FROM ghcr.io/katamaran-project/coq:8.16.1_iris-4.0.0_equations-1.3
RUN git clone https://github.com/katamaran-project/katamaran.git katamaran
WORKDIR /home/coq/katamaran
RUN git checkout ccs23
RUN eval $(opam env) && opam list && make Makefile.coq && make -j$(nproc) -f Makefile.coq pretty-timed | tee ./build.out

RUN sudo apt-get update && sudo apt-get install -y less nano vim emacs

CMD ["bash"]
