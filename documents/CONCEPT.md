# Introduction

[Elliptic curves][elliptic-curves], specifically over [Galois
fields][galois-field], have found multiple uses in blockchain applications. 
One particularly significant application is zero-knowledge proofs, which promise
significant capability enhancements, ranging from better onchain performance to
new operations. To this end, a whole constellation of different elliptic curves,
based on a huge range of Galois fields, have been proposed and designed. These
vary in their mathematical properties, intended use cases, and other features,
while still being broadly similar in terms of their basic foundations. Such
curves include, but aren't limited to:

* The [Pasta curves][pasta-curves]
* The [Grumpkin curve][grumpkin-curve]
* BLS12-381

This list is not complete, and is likely to grow larger as time passes. In
general, every blockchain, and its respective software ecosystem, tends to
settle on a different choice of elliptic curve(s) and associated Galois fields.

Plutus is no exception to this. Currently, there are no fewer than eight CIPs, in
various stages of adoption, which either directly, or indirectly, justify their
proposed extensions to Plutus by way of elliptic curves, finite field
arithmetic, or both:

* [CIP-0049][cip-49]
* [CIP-0058][cip-58]
* [CIP-0101][cip-101]
* [CIP-0121][cip-121]
* [CIP-0122][cip-122]
* [CIP-0123][cip-123]
* [CIP-0133][cip-133]
* [CIP-0381][cip-381]
 
These proposals are self-evidently useful, as shown by most of them being
adopted into Plutus Core. However, for an application developer who wants to
work over a specific elliptic curve, all of these proposed improvements suffer
from one of two problems. 

The first of these problems, as typified by CIP-0058, is an excess of
generality. You are given the pieces to (possibly) build the curve functionality
you need, but no help beyond that. This means a lot of work, likely involving
expertise (and concerns) far outside your domain of interest or knowledge.
Furthermore, you now become responsible for security considerations around
elliptic curve use. Lastly, if multiple application developers need logic around
a specific curve, this may end up being re-implemented multiple times by
different teams. None of these make the process _straightforward_, and in many
cases might be a hard obstacle to a working product even if it's technically
possible.

The second problem, typified by CIP-0381, is an excess of specificity. If an
application developer wants to work over a specifically-supported curve (such as
BLS12-381 in this case), this is a blessing from the correctness, optimization
and security point of view. However, if this isn't the curve they need, they are
left out in the cold. While it is conceivable for an application developer to
request the curve they need to have direct support in Plutus Core similar to
BLS12-381, this is impractical at best, and creates all the issues discussed
previously regarding incidental complexity and requiring expertise from other
domains.

Furthermore, there is an unspoken problem of having application developers being
forced to own the underlying primitives for their curve implementations. If
issues of performance or security are discovered, or even if some more
operations or generality are needed, the application developers must provide the
upgrade path. This can range from difficult to impossible, and must be
engineered for ahead of time. This just compounds the difficulties involved,
especially for developers who are not experts in either cryptographic security
or onchain performance.

# Our solution

We will create a two-part proof-of-concept system, named Grumpelstilskin, designed 
to allow
application developers to easily use any curve of their choice for
zero-knowledge proof verification oncahin. The first part of Grumpelstilskin
will be a 'working script' which, when given appropriate parameters via its
datum, will verify a zero-knowledge proof over a user-specified curve. This
script will be tested for correctness.

The second part of Grumpelstiltskin will be a [YTxP-based][ytxp] interface to
the 'working script', implemented in Plutarch. This interface will be
well-documented, easy to use, and flexible, with a focus of making life easy for
application developers who want to use zero-knowledge proofs. Thanks to our use
of YTxP, future performance, security and functionality improvements will not be
the responsibility of application developers who use Grumpelstilskin. This
second part will be distributed as an open-source project. 

We aim to build a minimum viable product, with the future goals of expanded
functionality, improved performance, as well as a full audit of the 'working
script'. Our choice of YTxP will make it minimally difficult to achieve this,
and will impose minimal friction on any application developers using
Grumpelstiltskin to build their products. 

# Milestones and deliverables

We describe the structure of the proposed work below. 

## Milestone 1: Key Galois field operations in Plutarch

We will implement key operations over user-parameterized Galois fields in
Plutarch. To achieve this generality, we will implement the following:

1. A representation of elements of a user-specified Galois field.
2. Field operations over the representation in 1.
3. Exponentiation operation over the representation in 1.

We will also write tests for general correctness of these operations, without a
specific field in mind. These tests will be done at the script level, rather
than the transaction level.

## Milestone 2: Key elliptic curve operations in Plutarch

We will implement key operations over user-parameterized elliptic curves. These
will use the work in Milestone 1 for Galois fields. For elliptic curves, we will
allow user-chosen curve constants, and well as user-chosen base and scalar
fields. To achieve this generality, we will need to implement the following:

1. A representation of points on user-specified elliptic curves, using the
   Galois field representation from Milestone 1.
2. Elliptic curve operations over the representation in 1. These will include at
   least the following:
   * Checking if a given point is on the curve
   * Elliptic curve point addition and scalar multiplication

We will also write tests for general correctness of these operations, without a
specific curve in mind. These tests will be done at the script level, rather
than the transaction level.

## Milestone 3: Plutarch core script for zero-knowledge proofs

Using the operations from Milestones 1 and 2, we will implement a script in 
Plutarch.
This script would verify a zero-knowledge proof over an arbitrary curve, over
arbitrary Galois fields, both specified as part of the datum. This would mint a
token if the proof holds. The goal of this script would be to serve as the
working component of a YTxP design.

## Milestone 4: Correctness for BLS12-381

To verify that the script from Milestone 3 is correct, we will test proof
verification against the BLS12-381 curve. This testing will be done against a
reference implementation using the BLS12-381 primitives provided by Plutus Core.

## Milestone 5: Plutarch YTxP wrapper

We will provide a [YTxP][ytxp]-using wrapper, implemented in Plutarch. It will
allow easy and convenient use of the core script implemented in Milestone 3. This 
wrapper will focus on convenience and ease of use, while also allowing
improvements in functionality, bugfixes and security fixes with minimum user
inconvenience. This wrapper will be published as an open-source project.

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

