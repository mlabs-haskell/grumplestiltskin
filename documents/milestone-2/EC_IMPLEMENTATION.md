# Implementation of elliptic curves for Grumplestiltskin

## Introduction

We implemented [elliptic curves][elliptic-curve] over Grumplestiltskin-defined
[Galois fields][galois-field], as required by Milestone 2. In particular, we
defined the following in `Grumplestiltskin.EllipticCurve`:

* SOP and `Data`-encoded types corresponding to points on elliptic curves over
  Galois fields as implemented in Milestone 1
* Group operations for these types (addition, inverse, scaling by integers)
* Conversions between SOP and `Data`-encoded types for points on elliptic curves

We made these definitions as efficient as possible, and as safe as is
reasonable. In particular, we aimed to reduce the amount of modulo reductions
required for group operations on elliptic curve points, similarly to our
strategy for Galois fields in Milestone 1.

To ensure correctness, we defined several kinds of tests in `test/ec/Main.hs`.
More specifically, we provide:

* A test enumerating every point accessible from a generator in a given elliptic
  curve;
* Property tests for group operations over elliptic curve points, as well as any
  attendant functionality for the data types representing them.
* Golden tests for code generation and performance of all operations.

## Goals and priorities

Our main priority was to extend the functionality from Milestone 1 to support
the group operations required of elliptic curves (using arbitrary curve
constants and field orders), while bein as efficient as Plutarch and UPLC
permit. This would allow us to determine how feasible using Grumplestiltskin
on-chain for elliptic curve computations would be.

Our goal was thus primarily implementing optimized elliptic curve group
operations, both by choosing good representations and also by implementing each
operation as optimally as these representations allow. We were somewhat
constrained by the requirement of using the Galois field representation as
defined in Milestone 1, but given its minimality, this wasn't significant.

The following sections will describe the architecture of the elliptic curve
module, and decisions taken to stay aligned with our priorities.

## Types

`Grumplestiltskin.EllipticCurve` defines three data types:

* `PECPoint`, representing a point on some elliptic curve over some Galois
  field, already in reduced form;
* `PECIntermediatePoint`, representing an 'intermediate computation' on
  `PECPoint`s; and
* `PECPointData`, a `Data`-encoded version of `PECPoint`.

Of these types, `PECIntermediatePoint` has the richest API, supporting the full
set of group operations, while `PECPoint` and `PECPointData` are more limited.

Following the lead of Milestone 1's representation of Galois fields, we chose
not to store (or even represent) the order of the field used to define elliptic
curve points, nor the curve constants of the curve whose points are being
represented. We discuss this choice in the 'Alternatives considered' section.

### SOP-encoded

We provide two SOP-encoded types, both representing elliptic curve points over
some Galois field. Their primary difference is that `PECPoint` uses
`PGFElement`s for its co-ordinates, while `PECIntermediatePoint` uses
`PGFIntermediate`s instead. Practically, this means that `PECPoint`s are always
in 'reduced form' (as per `PGFElement`), but `PECIntermediatePoint`s do not have
to be.

### `Data`-encoded

We define a single `Data`-encoded type `PECPointData`, representing elliptic
curve points over some Galois field. The difference between `PECPointData` and
its SOP-encoded equivalent `PECPoint` is a collection of extra fields,
representing both the field order (of type `PPositive`) and the curve constants
(both of type `PInteger`). `PECPointData` is supposed to store its two
co-ordinates in reduced form, such that the `PPositive` representing the field
order must be larger than the `PNatural`s representing both the co-ordinates.
Furthermore, the point (as defined by the two co-ordinates) must actually be on
the curve whose constants are specified. These constraints are defined and
checked in the decoding logic of the `PTryFrom` instance for `PECPointData`.

We chose not to make use of `PGFElementData`, as this would effectively store
the field order twice, redundantly. 

## Functions

There are two categories of functions for the data types defined in
`Grumplestiltskin.EllipticCurve`. First, there are conversion functions, which
handle conversions between the individual data types and help maintain their
specific invariants. Second, there are functions related to the elliptic curve
group operations. We also provide a function to verify whether a given point is
on a given curve, as `pecOnCurve`; as this capability is fairly straightforward,
we won't discuss it further.

### Conversions 

There are two pairs of conversions functions: 

* `pecToPoint` and `pecFromPoint`, designed to perform reductions modulo field
  order when explicitly requested; and
* `pecToData` and `pecFromData`, designed to convert to the `Data` encoding, and
  use the information in said `Data` encoding respectively.

`pecToPoint` and `pecFromPoint` effectively promote the `pgfToElem` and
`pgfFromElem` functions from `Grumplestiltskin.Galois` to work on elliptic curve
point representations instead. More specifically, `pecToPoint` reduces both of
the co-ordinates of the argument by the given field order, while `pecFromPoint`
'relaxes' into the intermediate computation type. Due to the need to represent
elliptic curve points as a sum type, `pecFromPoint` is not zero runtime cost
like `pgfFromElem`; we discuss the reasons for this, and why we decided to go
this way, in the 'Alternatives considered' section.

`pecToData` and `pecFromData` are designed to be the elliptic curve point
equivalents of `pgfToData` and `pgfFromData`. `pecToData` in particular is quite
similar, as it simply 'repacks' data, while also ensuring that the co-ordinates
are reduced by the field order. `pecFromData` however has a different form for
efficiency:

```haskell
pecFromData ::
    forall (r :: S -> Type) (s :: S).
    Term s PECPointData ->
    (Term s PECPoint -> Term s PPositive -> Term s PInteger -> Term s PInteger -> Term s r) ->
    Term s r
```

We chose this CPS-like solution due to the extra information encoded in
`PECPointData`, which is needed for almost every group operation. As `PECPoint`
keeps field order and curve constants implicit (and does not store them), a
'direct' unpacking would be quite inefficient when used 'naturally', as it would
require repeated field access to obtain the necessary additional parameters for
every group operation. While this could be improved by using `plet`, this is an
unnecessary bit of administrative work which our chosen solution prevents. We
discuss this design more in the 'Alternatives considered' section.

### Group operations

All group operations are defined over `PECIntermediatePoint`. Specifically, the
operations are implemented using the following functions:

* The group operator is `pecAdd` (as it corresponds to point addition);
* Group exponentiation is `pecScale`; and
* The inverse of an element can be found with `pecInvert`.

The neutral element of the group (that is, the point at infinity) is a
constructor of `PECIntermediatePoint`. We also provide a helper operation
`pecDouble`, which calculates `p + p = 2p` for any point `p`.

`pecAdd` and `pecInvert` are implemented in the standard way for affine
coordinates. In the case of `pecAdd`, in addition to the points being added, the
intended field order (as a `PPositive`) and the intended curve's @A@ constant
(as a `PInteger`) must be supplied as well. `pecScale` is implemented using
[exponentiation by squaring][exponentiation-by-squaring].

While in theory, `PAdditiveSemigroup`, `PAdditiveMonoid` and `PAdditiveGroup`
would be a good interface for these operations, due to our choices about
representation for `PECIntermediatePoint`, the methods provided by these type
classes are unsuitable. More specifically, `PECIntermediatePoint` keeps both the
@A@ constant of the curve the point is on, and the field order of the field used
to define its co-ordinates, implicit, which means any operation that requires
this information must be passed these two values explicitly. However, the type
classes mentioned above do not allow passing any additional data, thus forcing
us to define these operations as dedicated functions instead. We discuss our
reasoning behind these choices in the 'Alternatives considered' section.

## Alternatives considered

There are a range of possibilities, both from a high-level design perspective
and a lower-level implementation perspective, that we could have taken when
implementing the functionality of this Milestone. At the high level, a major
consideration was the type of coordinate system to use for elliptic curve
points, as a range of options exist. At the implementation level, we had to make
decisions around representations for any given chosen coordinate system, as well
as similar tradeoffs to Milestone 1 in terms of intermediate types and explicit
representation of elliptic curve constants. Lastly, our choices ended up making
the use of `PAdditiveGroup` and similar impossible: we will discuss our choices
here and why we ultimately decided that the less-pleasant interface was a
worthwhile tradeoff.

### Curve point coordinate system

One major choice we had to make was the choice of coordinate system to use for
curve points, as this would ultimately determine both what specific data we
would have to represent for any given point, as well as how group operations
would be implemented. There are several options:

* _Affine_, where only the two field elements (representing the `x`
  and `y` coordinates of the curve) are used. The point at infinity requires
  special treatment here.
* _Projective_, where an additional field element (the projective `z`) is used.
  This allows representing the point at infinity directly.
* _Jacobian_, which uses an additional field element similar to projective
  coordinates, but in a different way.
* _Chudnovsky-Jacobian_, which precomputes two exponents of the projective `z`
  used in many computations in the Jacobian representation.
* _Modified Jacobian_, which precomputes an exponent of the projective `z`
  multiplied by one of the curve constants.

Some noteworthy constraints and features of the chain, as well as Milestone 1's
implementation of field elements, that influenced our choice are as follows:

* All other things being equal, representations of points must be as small as
  possible, due to onchain memory limits.
* Precomputation is generally not feasible, both due to onchain space limits and
  the necessity of representing, and operating over, points on an arbitrary
  curve.
* Finding inverses of field elements is (relatively) inexpensive, thanks to the
  `ExpModInteger` builtin.
* Smaller code is preferable to avoid the transaction size limit becoming an
  issue.

To better conceptualize the choices that were put to us when choosing an
implementation, let us consider the costs of additions and doublings in each of
these representations, as all other operations ultimately depend on these. We
will base our descriptions on the algorithm descriptions provided by the _Handbook 
of Elliptic and Hyperelliptic Curve Cryptography_, as these would form the core
of any implementation, regardless of language or chosen representation. We will
describe the operations in terms of inversions (`I`), multiplications of field
elements (`M`) and squarings of field elements (`S`). We will assume that
operations over arguments in a particular representation produce results in the
same representation.

| Operation | Affine cost | Projective cost | Jacobian cost | Chudnovsky-Jacobian cost | Modified Jacobian cost |
|---|---|---|---|---|---|
| Addition of points | `I + 2M + 2S` | `12M + 2S` | `12M + 4S` | `11M + 3S` | `13M + 6S` |
| Doubling of point | `I + 2M + 2S` | `7M + 5S` | `4M + 6S` | `5M + 6S` | `4M + 4S` |

From this, we can see that all the non-affine representations essentially seek
to avoid finding any inverses. However, if we assume that these operations are
of essentially equal cost (as they are for us onchain) and re-examine these only
in terms of operation counts, the difference is striking:

| Operation | Affine cost | Projective cost | Jacobian cost | Chudnovsky-Jacobian cost | Modified Jacobian cost |
|---|---|---|---|---|---|
| Addition of points | 5 | 14 | 16 | 14 | 18 |
| Doubling of point | 5 | 12 | 10 | 11 | 8 |

In essentially all cases, using any representation other than the affine one
would significantly increase the amount of code (and work). This suggests affine
coordinates are the correct choice. The _Handbook_ supports our decision: in
situations where precomputations are unfeasible (as is the case with us),
Section 13.3.3 states the use of affine coordinates as the correct choice.

### Representation of elliptic curve points

Given our choice of affine coordinates, we require a sum type, as the point at
infinity cannot be represented as an affine coordinate. Setting `Data` encodings
aside for now, we are left with essentially two choices:

* A direct representation as an SOP encoding; or
* A [Boehm-Berrarducci encoding][bb].

Additionally, similarly to Milestone 1, we must consider whether auxiliary
information (field order and the curve constants) should be embedded in the
point's representation, or left implicit. Unlike in Milestone 1, this choice is
significant with regard to the interface over computations. With Galois fields,
a lot of operations (at least over the intermediate form) could be defined
without needing any information about field order; in the case of elliptic
curves, both addition and doubling require us knowing both the field order and
the curve's `a` constant in order to implement the operation at all. 

This essentially leaves the following possible combinations:

* Direct, implicit (what we chose)
* Direct, explicit
* Boehm-Berrarducci, implicit
* Boehm-Berrarducci, explicit

For clarity, we also provide the code that these representations would use. We
will use `FE` as a placeholder for the field element type.

```haskell
data DirectImplicit (s :: S) = 
    DIInfinity | 
    DIPoint (Term s FE) (Term s FE)

data DirectExplicit (s :: S) = 
    DEInfinity |
    DEPoint (Term s PPositive) (Term s PInteger) (Term s PInteger) (Term s FE) (Term s FE)

newtype BBImplicit (s :: S) = BBImplicit (
    forall (r :: S -> Type) .
    Term s (r :--> (FE :--> FE :--> r) :--> r)
    )

newtype BBExplicit (s :: S) = BBExplicit (
    forall (r :: S -> Type) . 
    Term s (r :--> (PPositive :--> PInteger :--> PInteger :--> FE :--> FE :--> r) :--> r)
    )
```

Considering the relative advantages and disadvantages of each choice, we can
immediately discard the direct explicit, and Boehm-Berrarducci implicit,
choices. While explicit representations (in either form) would allow us a more
convenient interface, the direct explicit representation is far too large to be
practical. For Boehm-Berrarducci forms (which are essentially lambdas), the
problem of size is not significant, which means that accepting the downsides of
implicit representations doesn't make sense. Thus, our choice came down to
direct implicit or Boehm-Berrarducci explicit, as the possible representations.

On paper, the explicit Boehm-Berrarducci representation is attractive: it is
compact, suits long computation chains (as it eliminates intermediate values),
allows the use of the `PAdditiveGroup` interface, and as we don't require
'accessor'-style operations, the biggest downside of a final encoding doesn't
affect us. However, this approach turned out to be untenable, as performance of
the explicit Boehm-Berrarducci form is unacceptably bad. We discuss this in more
detail in the 'Limitations and potential improvements' section, but in brief, it
is a problem we cannot avoid in general. Thus, only the direct implicit choice
remains, as performance must win out in general.

## Limitations and potential improvements

Some of the limitations we encountered stem from missing functionality onchain.
We describe these problems here, as well as discussing what improvements we
would need to overcome these limitations.

## Builtin arrays

One recent change in UPLC (specifically the implementation of [CIP-138
arrays][cip-138]) could have potentially been useful to us as a representation
of elliptic curve points. Our choice of SOP representation is forced on us due
to the double inefficiency of builtin lists as representations of tuples: not
only do they require more memory, their lack of random access makes them a bad
choice for most operations that elliptic curve points would require. Builtin
arrays theoretically solve both problems, as they are more compact and also have
constant-time indexing as a builtin operation.

However, limitations in the interface provided by CIP-138 meant that builtin
UPLC arrays as they are would not have been viable. More precisely, we lack any
built-in capabilities to transform arrays directly: every array transformation
must be done by first converting to a builtin list, applying the transformation
on the result, then converting back. This would completely defeat the point of
using CIP-138 arrays in the first place, as we would be incurring even higher
overheads than using builtin lists directly. While Plutarch's recent [pull
arrays][pull-array] could potentially have reduced some of the overheads, they
ultimately aren't sufficient, as many of the operations required are not linear
transformations. To see why, consider addition of two points in affine
coordinates `P = x1, y1` and `Q = x2, y2`. Assuming `P /= Q` and `P /= -Q`, we
have the following calculation:

```
let lambda = (y1 - y2) * recip (x1 - x2)
    x3 = lambda * lambda - x1 - x2
    y3 = lambda * (x1 - x3) - y1
  in x3, y3
```

We can see that `y3` depends on `x3`, which means that any array-based
representation of elliptic curve points could not perform this operation as a
linear transformation. Other representation choices suffer from similar issues.
At the same time, in languages with more capable array-based APIs, use of arrays
as representations for elliptic curve points (together with alternative
representations to speed up computations) are standard: for example,
[`elliptic-curve-solidity`][ec-solidity] uses the Jacobian form with arrays.

In order to enable such improvements, the API provided by CIP-138 would need
fundamental extensions. Two specific requirements are:

* Constructing builtin arrays directly (rather than by way of converting a
  builtin list); and
* An efficient way to perform non-linear transformations on arrays.

## Proper laziness

One major obstacle to our use of Boehm-Berrarducci forms stems from 'auxiliary
values', such as field order and curve constants. These are 'carried around' by
the data types, but don't change _within_ a computation. We are forced to make
them parameters, as Grumplestiltskin's stated goal is to support computations
over arbitrary Galois fields and elliptic curves. However, this leads to a
problem of excessive evaluation, which cannot be avoided with currently
available UPLC primitives.

This problem can manifest itself in very subtle ways. Consider the group
operation for curve points: if either argument curve point is the point at
infinity, we produce the other argument, as the point at infinity is the neutral
element. Ideally, in such a case, we would simply return the argument in
question unchanged, but in a Boehm-Berrarducci form, to even _establish_ this
requires calling the argument's continuation. Thus, if we assume the
continuation of the group operation result provides `whenInf` and `whenNot`
handlers, and we have argument continuations `k1` and `k2`, we are forced to
write something like

```haskell
k1 (k2 whenInf whenNot) $ \x1 y1 order curveA curveB -> 
    k2 (k1 whenInf whenNot) $ \x2 y2 _ _ _ -> 
        -- rest of the computation
```

As UPLC is strict, the resulting computation ends up evaluating far more than it
should: we are forced to evaluate `k2 whenInf whenNot` every time (even if's not
used), and if the first argument point is not the point at infinity, we are
forced to evaluate `k1 whenInf whenNot` even if the second point is not the
point at infinity either! The only way we can attempt to resolve this is by
using `Delay` and `Force` constructions from UPLC, which would require us to
change our Plutarch data type to something akin to the following:

```haskell
newtype BBExplicit' (s :: S) = BBExplicit' (
    forall (r :: S -> Type) . 
    Term s (PDelayed r :--> (PPositive :--> PInteger :--> PInteger :--> FE :--> FE :--> r) :--> r)
    )
```

However, this solution merely kicks the problem down the road. As `Delay`ed
computations in UPLC have no 'memory' of being evaluated, every `Force` is
required to recompute it, even if the computation is referentially transparent.
In our case, this could mean re-evaluating a potentially large chain of
computations we have 'built up' over time repeatedly, even though the answer
never changes. This means we must take a performance penalty no matter what we
do.

Notably, in a non-strict language like Haskell, this problem does not arise, as
if a continuation call is never needed, it won't be evaluated, rendering the
problem above essentially impossible. However, GHC Haskell contains provisions
for not re-evaluating lazy computations after the first time they are demanded,
essentially making it a '`Force` with memory'. No such construction exists in
UPLC, and while in specific cases it could be simulated with existing
mechanisms, in general, it is not possible.

To resolve this performance problem (and indeed, what prevented us from using
the Boehm-Berrarducci approach in the first place) would require a proper
treatment of laziness in UPLC. Ideally, something akin to [promises][promise]
would work here, effectively providing a 'boxed computation' type which has the
ability to cache the result of that computation for future requests for the
answer.

[elliptic-curve]: https://en.wikipedia.org/wiki/Elliptic_curve
[exponentiation-by-squaring]: https://en.wikipedia.org/wiki/Exponentiation_by_squaring
[galois-field]: https://en.wikipedia.org/wiki/Finite_field
[bb]: https://okmij.org/ftp/tagless-final/course/Boehm-Berarducci.html
[cip-138]: https://cips.cardano.org/cip/CIP-138
[pull-array]: https://www.mlabs.city/blog/performance-pull-arrays-and-plutarch
[ec-solidity]: https://github.com/witnet/elliptic-curve-solidity/blob/master/contracts/EllipticCurve.sol
[promises]: https://en.wikipedia.org/wiki/Futures_and_promises
