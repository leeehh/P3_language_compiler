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
docker run -it p3c
```

### Compilation

To make a executable binary release, simply run

```
make all
```

### Test

Test cases lie within the `test/` folder.

```
./Driver.native test/sample.ppp
```

---

## Maintainers

* **Ling Li** - liling14(AT)tsinghua.org.cn

* **Shengyuan Wang** - wwssyy(AT)tsinghua.edu.cn
