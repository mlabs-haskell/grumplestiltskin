# Grumplestiltskin

## What is this project?

Grumplestiltskin is a [YTxP][ytxp]-powered framework for zero-knowledge proof
verification and signature verification. It will allow the use of any curve, as
specified by the user of the framework. Its use of YTxP will make it easy to
use as part of other projects, and easy to update (for fixes, feature
improvement and optimizations) with minimal effort from its users.

We will build Grumplestiltskin in two phases:

* A 'concept' phase, which will put in just enough functionality to verify
  zero-knowledge proofs over user-specified curves; and
* A 'product' phase, which will fill out the functionality with signature
  verification as well, plus an audit, conformance cases against specific
  curves, and performance improvements.

The 'concept' phase will already yield a usable framework at its completion,
though the 'product' phase will ensure that it is convenient to use in
production and fully-featured.

## How to find out more

* `CONCEPT.md` motivates and describes the 'concept' phase of the project.
* `PRODUCT.md` motivates and describes the 'product' phase of the project.

[ytxp]: https://www.mlabs.city/blog/an-introduction-to-the-concepts-behind-ytxp-architecture 
