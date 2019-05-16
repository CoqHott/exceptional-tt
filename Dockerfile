FROM coqorg/coq:8.8

WORKDIR /home/coq/exceptional-tt

COPY . .

RUN ["/bin/bash", "--login", "-c", "set -x \
  && opam update \
  && opam pin -y -n add coq-exceptional-tt . \
  && opam install -y -v -j $NJOBS coq-exceptional-tt \
  && opam list \
  && opam clean -a -c -s --logs"]
