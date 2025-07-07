# CDCL(OCAC)

This is an adapted version of [*CVC5*](https://github.com/cvc5/cvc5) tailored for solving **OMT over Nonlinear Real Arithmetic (OMT(NRA))** problems. Below is a quick guide to compiling and running the solver.

## 🛠️ Compile

Use the following command to configure and build:

```bash
./configure.sh --auto-download --poly --cocoa
cd build/
make -j12
```

## ▶️ Run

Execute the solver with your SMT-LIB2 input file:

```bash
./build/bin/cvc5 your_input.smt2
```

## 📄 Example

```smt2
(set-logic OMT_QF_NRA)

(declare-fun x () Real)
(declare-fun y () Real)

(assert (and 
  (>= x 0)
  (>= y 0)
  (<= x 10)
  (<= y 10)
  (>= (- (* x x) y) 1)
))

(minimize (+ (* x x) (* y y)))

(check-sat)
(get-objectives)
(get-model)
```

## ⚠️ Important Note

Be sure to include the following logic tag at the beginning of your `.smt2` file:

```smt2
(set-logic OMT_QF_NRA)
```

Otherwise, the solver may crash with:

```
Segmentation fault (core dumped)
```



-------------------------------------------------------

[![License: BSD](
    https://img.shields.io/badge/License-BSD%203--Clause-blue.svg)](
        https://opensource.org/licenses/BSD-3-Clause)
![CI](https://github.com/cvc5/cvc5/workflows/CI/badge.svg)
[![Coverage](
  https://img.shields.io/endpoint?url=https://cvc5.stanford.edu/downloads/builds/coverage/nightly-coverage.json)](
    https://cvc5.stanford.edu/downloads/builds/coverage)

cvc5
===============================================================================

cvc5 is a tool for determining the satisfiability of a first order formula
modulo a first order theory (or a combination of such theories).  It is the
fifth in the Cooperating Validity Checker family of tools (CVC, CVC Lite,
CVC3, CVC4) but does not directly incorporate code from any previous version
prior to CVC4.

If you are using cvc5 in your work, or incorporating it into software of your
own, we invite you to send us a description and link to your
project/software, so that we can link it on our [Third Party
Applications](https://cvc5.github.io/third-party-applications.html) page.

cvc5 is intended to be an open and extensible SMT engine.  It can be used as a
stand-alone tool or as a library.  It has been designed to increase the
performance and reduce the memory overhead of its predecessors.  It is written
entirely in C++ and is released under an open-source software license (see file
[COPYING](https://github.com/cvc5/cvc5/blob/main/COPYING)).


Website
-------------------------------------------------------------------------------
cvc5's website  is available at:
https://cvc5.github.io/

Documentation
-------------------------------------------------------------------------------
Documentation for users of cvc5 is available at:
https://cvc5.github.io/docs/

Documentation for developers is available at:
https://github.com/cvc5/cvc5/wiki/Developer-Guide

Download
-------------------------------------------------------------------------------

The latest version of cvc5 is available on GitHub:
https://github.com/cvc5/cvc5

Source tar balls and binaries for releases of the
[main branch](https://github.com/cvc5/cvc5) can be
found [here](https://github.com/cvc5/cvc5/releases).
Nightly builds are available [here](https://cvc5.github.io/downloads).


Build and Dependencies
-------------------------------------------------------------------------------

cvc5 can be built on Linux and macOS.  For Windows, cvc5 can be cross-compiled
using Mingw-w64.

For detailed build and installation instructions on these platforms,
see file [INSTALL.rst](https://github.com/cvc5/cvc5/blob/main/INSTALL.rst).


Bug Reports
-------------------------------------------------------------------------------

If you need to report a bug with cvc5, or make a feature request, please visit
our bugtracker at our [GitHub issues](https://github.com/cvc5/cvc5/issues)
page. We are very grateful for bug reports,  as they help us improve cvc5.


Contributing
-------------------------------------------------------------------------------

Please refer to our [contributing guidelines](CONTRIBUTING.md).


Authors
-------------------------------------------------------------------------------

For a full list of authors, please refer to the
[AUTHORS](https://github.com/cvc5/cvc5/blob/main/AUTHORS) file.
