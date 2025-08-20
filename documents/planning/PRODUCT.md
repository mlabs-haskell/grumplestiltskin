# Introduction

[Elliptic curves][elliptic-curves], specifically over [Galois
fields][galois-field], have found multiple uses in blockchain applications. Two
in particular stand out:

* Signature schemes, specifically signature verification
* Zero-knowledge proof verification

The first of these is critical for sidechains, or inter-chain operations, while
the second promises significant improvements in what we can do onchain, ranging
from better performance to brand new operations. To both of these ends, there
now exists a whole constellation of different elliptic curves, based on a huge
range of Galois fields. These vary in their properties, use cases and other
features, but are broad enough that [generalized
solutions][elliptic-curve-solidity] to work with them exist.

On the Cardano blockchain, the only such general solution, suitable for the wide
range of current and future needs of application developers using elliptic
curves, is Grumplestiltskin, which we implemented as a minimum viable product.
As the first design of its kind, it both collected the necessary core operations
needed for elliptic curve work, it also provides a ready-to-use zero-knowledge
proof verification interface. Furthermore, thanks to its [YTxP-based][ytxp]
design, it is easily upgraded and improved, with minimal friction for
application developers. We believe that this design, together with its
usefulness, makes it uniquely important in the Cardano ecosystem.

However, in spite of this, Grumplestiltskin still lacks certain things to make
it a robust, ready-to-use product. Specifically, the following limitations
persist:

* Grumplestiltskin cannot verify signatures based on elliptic curves.
* We have no firm evidence that any specific curve works, or how well it works.
* Performance, and security, had to take a back seat relative correctness, due
  to time and budget constraints.
* The interface to Grumplestiltskin's functionality is only available in
  Plutarch.

These limitations currently make Grumplestiltskin less than an ideal solution
for being the future of elliptic curve work on the Cardano blockchain. This is
understandable given its MVP status, but regrettable due to the potential it
has.

# Our solution

We propose to extend Grumplestiltskin to make it a
fully-fledged, 'industrial strength' solution to both zero-knowledge proof
verification, as well as signature verification, over user-specified elliptic
curves. To that end, we will deliver the following:

* An additional 'core script' to perform signature verification over arbitrary
  elliptic curves. This will be deployed, and used, via YTxP, similarly to
  Grumplestiltskin's existing functionality for checking zero-knowledge proofs.
* Specific conformance cases, and tests, to ensure that the Pasta curves, as
  well as the Grumpkin curve, work as expected.
* Benchmarks for the Pasta curves, the Grumpkin curve, and all their underlying
  Galois fields, to assess their execution unit and memory use for both
  signature verification and zero-knowledge proof verification.
* Optimizations of all Grumplestiltskin functionality (including the new
  functionality for signature verification), with priority given to improving
  the Pasta and Grumpkin curves' performance specifically.
* A full audit of Grumplestiltskin's existing and new functionality,
  post-optimization, to ensure no security (or other) issues exist. We will
  address any issues found, and deploy fixes using YTxP.
* A second wrapper for use of the functionality of Grumplestiltskin, implemented
  in Aiken. This will match the functionality of the existing Plutarch wrapper
  as much as permitted by the difference in languages.

We believe this will make Grumplestiltskin the go-to solution for doing either
signature verification or zero-knowledge proof verification on the Cardano
blockchain. Furthermore, we believe it could serve as a platform for future work
using elliptic curves, thanks to the convenience of YTxP.

# Milestones and deliverables

We describe the structure of the proposed work below.

## Milestone 1: Plutarch core script for signature verification

We will implement a script in Plutarch. This script would verify a signature
over an arbitrary curve, over arbitrary Galois fields, both specified as part of
the datum. This would mint a token if the signature is valid. The goal of this
script would be to serve as the working component of a YTxP design, similar to
Grumpelstiltskin's script to verify zero-knowledge proofs.

We will supplement the existing YTxP-based wrapper for Grumplestiltskin to allow
the use of this new script from its existing interface. The fix will be deployed
using YTxP.

## Milestone 2: Pasta and Grumpkin conformance

We will write script-level conformance tests to ensure that the following curves
behave as expected with all existing Grumplestiltskin functionality, as well as
the new functionality in Milestone 1:

* The Pallas [Pasta curve][pasta-curves]
* The Vesta [Pasta curve][pasta-curves]
* The [Grumpkin curve][grumpkin-curve]

These tests will assess both the curves and their underlying Galois fields (base
and scalar) for correctness. We will also implement benchmarks to assess the
performance of the operations for these three curves, in terms of execution unit
and memory use.

## Milestone 3: Performance tuning

Using the benchmarks produced as part of Milestone 2, we will attempt to improve
the performance of existing Grumplestiltskin functionality, as well as the new
functionality in Milestone 1. This will attempt to reduce both memory cost and
execution unit cost. Ideally, any improvements will be as general as possible,
but the focus will be to optimize operations for the three curves from Milestone
2, as well as the Galois fields they use.

## Milestone 4: Audit of core scripts 

We will audit all the code from Grumplestiltskin, both existing and added as
part of Milestone 1, together with any Milestone 3 optimizations. This will
ensure that none of the functionality is vulnerable to either typical onchain
security risks, or any specific risks related to elliptic curve-based signature
schemes or zero-knowledge proof verification.

## Milestone 5: Response to audit

Based on the results of the Milestone 4 audit, we will make any corrections
necessary to ensure that there are no security risks around any Grumplestiltskin
code. We will also address any other feedback the audit produces. We will deploy
any corrections, as well as the now-audited Milestone 3 optimizations, using
YTxP.

## Milestone 6: Aiken YTxP wrapper

We will provide a [YTxP][ytxp]-using wrapper, implemented in Aiken. It will act
as a direct counterpart to the existing Plutarch wrapper, with as much
similarity of the interface as Aiken allows. This wrapper will be published as
an open-source project.

[ytxp]: https://www.mlabs.city/blog/an-introduction-to-the-concepts-behind-ytxp-architecture
[elliptic-curves]: https://en.wikipedia.org/wiki/Elliptic_curve
[galois-field]: https://en.wikipedia.org/wiki/Finite_field
[pasta-curves]: https://o1-labs.github.io/proof-systems/specs/pasta.html
[grumpkin-curve]: https://aztecprotocol.github.io/aztec-connect/primitives.html#2-grumpkin---a-curve-on-top-of-bn-254-for-snark-efficient-group-operations
[cip-49]: https://github.com/cardano-foundation/CIPs/tree/master/CIP-0049
[cip-58]: https://github.com/cardano-foundation/CIPs/tree/master/CIP-0058
[cip-101]: https://github.com/cardano-foundation/CIPs/tree/master/CIP-0101
[cip-121]: https://github.com/cardano-foundation/CIPs/tree/master/CIP-0121
[cip-122]: https://github.com/cardano-foundation/CIPs/tree/master/CIP-0122
[cip-123]: https://github.com/cardano-foundation/CIPs/tree/master/CIP-0123
[cip-133]: https://github.com/cardano-foundation/CIPs/tree/master/CIP-0133
[cip-381]: https://github.com/cardano-foundation/CIPs/tree/master/CIP-0381
[elliptic-curve-solidity]: https://github.com/witnet/elliptic-curve-solidity
