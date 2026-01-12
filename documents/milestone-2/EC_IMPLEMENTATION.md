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
the field order twice, redundantly. [TODO: Maybe remove that field from
`PGFElementData` then?]

## Functions

There are two categories of functions for the data types defined in
`Grumplestiltskin.EllipticCurve`. First, there are conversion functions, which
handle conversions between the individual data types and help maintain their
specific invariants. Second, there are functions related to the elliptic curve
group operations. 

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

## Alternatives considered

[TODO: Fill in]

[elliptic-curve]: https://en.wikipedia.org/wiki/Elliptic_curve
[exponentiation-by-squaring]: https://en.wikipedia.org/wiki/Exponentiation_by_squaring
[galois-field]: https://en.wikipedia.org/wiki/Finite_field

