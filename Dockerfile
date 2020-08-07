FROM coqorg/coq:8.4.6

RUN opam pin add menhir 20171222 -y
RUN sudo apt-get update && sudo apt-get install subversion -y && sudo apt-get autoremove && sudo apt-get clean
