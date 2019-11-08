FROM coqorg/coq:8.4.6

RUN opam pin add menhir 20171222 -y
RUN sudo apt-get update 
RUN sudo apt-get install subversion -y
RUN sudo apt-get autoremove
RUN sudo apt-get clean
