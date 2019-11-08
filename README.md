# P3 Compiler

## Introduction

This is the P3 Compiler project.

---

## Get Started

### Environment

#### Prerequisites

* Coq Proof Assistant, version 8.4pl6
* Objective Caml compiler, version 4.02.3
* Menhir Parser Generator, version 20171222

#### Using Docker

It is recommended that you use Docker to deploy an out-of-box envrionment. Just install Docker and run the following command:

```
docker build --tag=p3c .
docker run -it -v $(pwd):/home/coq/p3c p3c
```

Then change the directory to p3c in the container

```
cd p3c
```

### Compilation

To make a executable binary release, simply run

```
make all
```

### Test

Test cases lie within the `test/` folder.

Print the AST

```
./p3c -print-ast test/beautify.ppp
```
or
```
./p3c -print-ast test/original.ppp
```

---

## Maintainers

* **Ling Li** - liling14(AT)tsinghua.org.cn

* **Shengyuan Wang** - wwssyy(AT)tsinghua.edu.cn

* **Huanghua Li** - lihh18(AT)mails.tsinghua.edu.cn
