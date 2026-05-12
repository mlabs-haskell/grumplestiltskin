# Recommendations for improvements

## Introduction

[TODO: More]

Throughout, as a point of comparison, we will refer to the
[`elliptic-curve-solidity`][ec-solidity] library. This particular library is
used as a point of comparison for several reasons:

* It fulfils the same role in its ecosystem as Grumplestiltskin would for
  Cardano; 
* It demonstrates typical implementation choices (and performance) given a
  'standard' collection of operations in most programming languages; and
* Its practical limits are what could be expected from any reasonable onchain
  implementation of the functionality we are interested in.

We make use of several terms and definitions from the Milestone 3 (and
transitively, Milestone 2) reports. In particular, we assume that the terms
'direct representation' and 'indirect representation' are familiar to the
reader, as well as how these two styles of representation are applied to both
finite field elements (and their extensions) and elliptic curve points.
Additionally, we assume the reader is familiar with the distinction between
affine and projective representations of elliptic curve points.

## Limitations as they currently stand

Based on the available capabilities of UPLC at the time of writing this report,
Grumplestiltskin suffers from performance problems that are not possible to
address. In practice, this makes it unusable as a basis for onchain operations
involving elliptic curves beyond small and simple cases. These performance
issues cannot be addressed as they stem from choices in UPLC. More precisely,
the following key issues exist:

* Lack of mutability or call-by-need evaluation means that we are forced to
  choose between over-evaluation (wasting time) or over-allocation (wasting
  memory).
* Limited support for array computations, combined with relatively cheap modular
  inversions, makes non-affine representations unworkable.

Specifics of why these issues arise are presented, with benchmark evidence, in
the Milestone 3 report. 

[TODO: Fill in]

## Proposed improvements

In light of the above limitations, we believe there are three possible
improvements that could be made to UPLC. Furthermore, we describe why it is not
possible to fix these changes 'a level above' by using a more sophisticated set
of techniques in Plutarch (or indeed, any other similar language or tool).

### Direct call-by-need support

[TODO: Lead in]

The lack of call-by-need limits not only Grumplestiltskin's performance, but
also Cardano scripts and dApps more generally. An [active CPS][cps-28] exists
around this issue, and a [draft solution][cps-28-impl] has been proposed and
tested for performance. This solution essentially 'retrofits' `Delay` and
`Force` to cache the result of the first `Force` to avoid re-evaluation,
mimicking the support for call-by-need found in languages like GHC Haskell. This
solution directly addresses the inevitable re-evaluation problem described in
Milestone 3 for the indirect representation, which would improve performance
significantly. However, this solution has yet to be adopted, and no clear path
towards its adoption exists at the time of writing.

[TODO: More?]

### Improved arrays

[TODO: Fill in]

### Mutability

Mutability would allow us to address the performance issues highlighted by
Milestone 3, as it would allow the use of direct representations while
simultaneously avoiding unnecessary intermediates. This is particularly relevant
in cases where the number of intermediates is both large and predictable: for
example, when performing an elliptic curve scalar multiplication, we can
eliminate essentially all intermediate values using mutability without even
having to give up referential transparency. 

[TODO: Fill in]

### Why do these require UPLC-level changes?

[TODO: Justify]

At a glance, it would appear that array improvements could be done without
UPLC-level changes. A major piece of evidence in that direction is Plutarch's 
implementation of pull arrays [demonstrated significant improvements][plutarch-pull-array] 
without requiring additional UPLC-level array primitives. In particular, pull
arrays naturally have the ability to 'fuse away' intermediate computations,
which is a significant problem with any direct representation. Unfortunately,
such solutions in general, and pull arrays in particular, cannot address the
performance limitations of Grumplestiltskin. [TODO: Explain]

[TODO: More]

## Conclusion

[TODO: Justify]

[ec-solidity]: https://github.com/witnet/elliptic-curve-solidity
[cps-28]: https://github.com/mlabs-haskell/CIPs/blob/laziness/CPS-0028/README.md
[cps-28-impl]: https://github.com/user-attachments/files/26065364/lazy-delay-force.pdf
[plutarch-pull-array]: https://www.mlabs.city/blog/performance-pull-arrays-and-plutarch
