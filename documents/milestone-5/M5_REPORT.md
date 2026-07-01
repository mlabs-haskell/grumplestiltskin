# Milestone 5 report

## Introduction

As the conclusions presented in the [Milestone 3 report][M3] demonstrate, the
current limitations of UPLC are such that implementing a parametric onchain
zero-knowledge proof verifier is not viable. Performance problems that emerged
when attempting to implement operations on higher-order field extensions, and
curves over these extensions, were so severe as to render our initial goal
intractable. Thus, we were forced to halt our attempt to develop
Grumplestiltskin as a verification framework supporting arbitrary curves. At the
same time, the limitations we found originate from contingent (rather than
essential) features of UPLC; more precisely, UPLC could be modified to make our
original goal viable, or at least more viable than at the time of writing.

In this report, we will outline three proposed changes to UPLC: call-by-need
evaluation, mutability, and a better implementation of arrays. We describe how
each of these could address the performance problems we encountered, as well as
what costs and benefits outside of those specific problems would arise with each
of these changes. Briefly, we conclude the following:

- Call-by-need evaluation is both a minimally-disruptive change, and also one
  that has a chance to improve our performance. However, we don't believe that
  the improvements would be enough to solve the problems we describe in the
  Milestone 3 report.
- Mutability in UPLC would give us the capability to solve our performance
  problems with a high degree of certainty. However, the consequences of this
  change to UPLC are too severe to recommend.
- Better arrays in UPLC are a 'middle ground' between the power of mutability
  and the low-impact nature of call-by-need evaluation. It is likely to give us
  enough power to solve our performance problems, while not being as disruptive
  as mutability.

## Call-by-need (laziness)

In the [Milestone 3 report][M3], we identified excessive re-evaluation of
previously-computed results as a major cause of the performance degradation we
encountered. Indirect representations in particular suffered as a result of this
problem. In the context of a functional language (which UPLC principally is),
one straightforward solution to such an issue is adding support for
[_call-by-need_][call-by-need] (also commonly known as 'lazy') evaluation. This
is a well-studied implementation choice, and happens to be the evaluation
strategy used by GHC.

More specifically, based on the Milestone 3 benchmarks, the most efficient way
to represent curve points over finite field extensions was an indirect
representation[^1], which makes use of [Boehm-Berrarducci][bb] forms. However,
this representation leads to severe performance degradation due to repeat
re-evaluation of previously-computed terms. This is most visible in the context
of point addition, which, due to its fundamental nature, has a significant
impact on other operations (such as point scaling). The primary source of this
performance problem is the need to constantly determine whether some previous
result happens to be the point at infinity or not. This is an unavoidable
requirement: our code must treat the point at infinity as an additive identity,
but our choice of an affine representation also forces the use of a sum type.

While UPLC supports the ability to defer evaluation with the `delay` primitive
(and a corresponding `force` primitive to demand evaluation), these primitives
do not currently provide any kind of memoization or caching of prior results.
This design choice, known colloquially as _sharing_, is the one taken by GHC,
and ultimately almost every language that supports call-by-need evaluation.
While strictly speaking, call-by-need evaluation does not _require_ sharing, its
benefits are not realizable without it. Thus, by this logic, we believe that
UPLC does not support 'true' call-by-need at this time, unlike, for example,
GHC.

This problem is compounded by the fact that, unlike most other languages with
non-caching 'delay' and 'force' constructions, there is no available mechanism
to provide memoization or sharing. This is in contrast to a language such as
Purescript: despite not having 'language level' support for sharing, it provides
the tools needed to implement it if needed. UPLC has no mechanism for this
whatsoever, and thus, would _need_ 'language level' support of sharing to work.

To make the problem clearer, we provide the following example. Consider the
following Haskell expression:

```haskell
-- idiomatic
let x = 10 ^ 10 in x + x

-- this is equivalent to
(\x -> x + x) (10^10)
```

If this code were compiled with GHC and executed, the expression `10^10` would
be computed once, and cached. Thus, the expression `x + x` would not have to
re-compute `10^10`. If we attempt to mimic this in UPLC, we cannot do this: the
best we can do is the following (using slightly simplified syntax):

```
(\x -> force x + force x) (delay (10^10))
```

The use of `delay` here will mean that `10^10` will not be evaluated as soon as
`(delay (10^10))` is passed to the function. Instead, we will only evaluate
`10^10` when the variable `x` is `force`d. However, in this situation, `10^10`
will end up being computed _twice_: once per use of `force` on `x`. This stems
from `x` not 'knowing' that it has already been computed.

While the given example is somewhat trivial, in practice, the kind of 'repeat
evaluation' which this potentially forces on us could require re-computing
results many times, and said results might be large computations. Furthermore,
while code re-organization can potentially solve some of these issues, it is not
possible in general: in particular, it isn't at all apparent how our specific
problem could have been solved in this way. While compilation frameworks could
sometimes avoid such problems through clever optimizations, no framework that
targets UPLC is currently capable of this.

Call-by-need with evaluation would immediately solve this problem, by simply
caching the results of computations that have already been evaluated. This would
require no input by either users of a framework targeting UPLC, nor the
framework itself. This would likely provide a significant boost to our most
efficient representation, as well as many other idioms familiar to functional
programmers in general, and Haskellers in particular. This last aspect is of
non-trivial benefit to framework maintainers, as at least two UPLC code
frameworks (Plinth and Plutarch) embed themselves in Haskell and target a
Haskell-familiar audience.

Call-by-need evaluation would also be minimally disruptive to UPLC at it exists
now. While there are several ways that it could be implemented, the most
straightforward would be to simply modify the behavior of the existing `force`
and `delay` builtins to perform caching or memoization. This may require
nontrivial modifications to the UPLC evaluation machinery, but should not affect
UPLC's public API at all. Call-by-need evaluation is well-understood, with a
solid theoretical basis, has been implemented in other functional languages, and
[initial exploratory work][UPLC-Laziness] on modifying `force` and `delay` in
UPLC has shown the approach to be viable.

However, there are some drawbacks to call-by-need as a solution to our problems.
While we are certain that call-by-need evaluation will improve the performance
of our best implementation, we are less certain that the improvement will be
significant enough to make onchain verification viable given protocol limits.
Strictly speaking, it is impossible to know this, because this change may well
necessitate adjusting the costing parameters for `force` and `delay`, as these
builtins would now do more work at a hardware level than they do at present.
Determining the new costing parameters is, on its own, a nontrivial problem, and
likely depends on the details of the changes to UPLC evaluation machinery.

Furthermore, even on the assumption that call-by-need does lead to a viable
onchain verifier, it still necessitates the use of a Boehm-Berarducci
representation of curve points for curves over higher order finite field
extensions, which is counter-intuitive and awkward to work with.
Boehm-Berarducci forms force us to use a continuation-passing style in
functions, which generates a significant amount of syntactic noise. A simple
example from `Grumplestiltskin.Degree2.EllipticCurveID` demonstrates this
awkwardness clearly:

```haskell
pec2Double ::
    forall (s :: S).
    Term s PEC2Intermediate -> Term s PEC2Intermediate
pec2Double t = pmatch t $ \(PEC2Intermediate k1) ->
    pcon $ PEC2Intermediate $ plam $ \fieldMod rSquared curveA whenInf whenNot ->
        k1
            # fieldMod
            # rSquared
            # curveA
            # whenInf
            # plam
                ( \x y ->
                    pec2Double' # fieldMod # rSquared # curveA # whenInf # whenNot # pd2FromElem x # pd2FromElem y # y
                )
```

While this is not necessarily a decisive consideration, it is worth noting that
from the developer's point of view, unless heavily supported by a framework
'behind the scenes', the inconvenience of benefitting from the performance of
call-by-need with sharing may be significant. It is worth noting here that
Plutarch has the greatest support for this style of implementation: Plinth and
Aiken make writing this kind of code either utterly impossible or so awkward as
to not be worth attempting.

## Mutability

The second option for modifying UPLC so that it can facilitate performant
onchain verification is to add _mutability_ to the language. Mutability would,
effectively, allow us to achieve the benefits of call-by-need evaluation by
performing our own caching and memoization. Whereas in call-by-need, the
evaluation machinery would handle storing previously computed results so that
they do not need to be re-evaluated when passed to subsequent computations, UPLC
with mutability would allow us to store the results directly in a mutable
variable that could be passed to subsequent computations.

For our purposes, 'local' mutability would suffice. By this we mean mutability
that is essentially analogous to Haskell's `ST`, where variables must be
explicitly tagged as mutable and cannot escape their computational context. This
is in contrast to 'global' mutability, which is the default in many other
onchain languages: any and every reference is implicitly mutable with no
designation.

Furthermore, mutability in UPLC would enable performance gains that do not
relate to Grumplestiltskin at all, in a broad range of settings. This is a
non-trivial merit: due to the environment in which UPLC is run, performance is
paramount, both in terms of restricting memory use and restricting computation
time. It is for this reason that mutability is seen as advantageous: there exist
numerous algorithms and tasks wherein mutability provides an asymptotic speedup
[that cannot be replicated otherwise][lazy-functional-state-threads]. Lastly, it
is worth noting that mutability is an extremely familiar capability to most
developers, regardless of their language background: having mutability would
thus allow much more code re-use and parsimony, as compared to what UPLC (and
the frameworks that target it) permit now.

To see how mutability can enable improvements in our specific case, we consider
an implementation of elliptic curve operations in [Solidity][SOLIDITY], which is
used in live contracts. In the following example, we can see a direct
translation of elliptic curve point scaling using the Jacobian representation:

```solidity
/// @dev Multiply point (x, y, z) times d.
/// @param _d scalar to multiply
/// @param _x coordinate x of P1
/// @param _y coordinate y of P1
/// @param _z coordinate z of P1
/// @param _aa constant of curve
/// @param _pp the modulus
/// @return (qx, qy, qz) d*P1 in Jacobian
function jacMul(
        uint256 _d,
        uint256 _x,
        uint256 _y,
        uint256 _z,
        uint256 _aa,
        uint256 _pp
    ) 
    internal pure 
    returns (uint256, uint256, uint256) 
{
    // Early return in case that `_d == 0`
    if (_d == 0) {
        return (_x, _y, _z);
    }

    uint256 remaining = _d;
    uint256 qx = 0;
    uint256 qy = 0;
    uint256 qz = 1;

    // Double and add algorithm
    while (remaining != 0) {
        if ((remaining & 1) != 0) {
            (qx, qy, qz) = jacAdd(qx, qy, qz, _x, _y, _z, _pp);
        }
        remaining = remaining / 2;
        (_x, _y, _z) = jacDouble(_x, _y, _z, _aa, _pp);
    }
    return (qx, qy, qz);
}
```

We immediately observe the naturality and clarity of the implementation:
Solidity-specific syntax aside, this is close to a word-for-word translation of
the description of this operation that could be obtained from any reference on
the subject, whether mathematical or code-based. Furthermore, unlike our
attempts in Milestone 3, no recomputation is required, due to the natural
ability to cache results given by mutability.

At the same time, however, mutability has significant knock-on effects, not only
for UPLC, but for Cardano as a whole. To see why, let us consider exactly how
languages with the capability of 'local' mutation implement it, taking GHC
Haskell as an example. Here, 'local' mutation is provided by way of the `ST`
monad, along with the function

```haskell
runST :: forall a . (forall s . ST s a) -> a
```

This function uses a rank-2 type to ensure that any attempt to 'leak' mutable
state out of `ST` cannot compile:

```haskell
-- This will not compile!
bad :: ST s (STRef s a) -> STRef s a
bad = runST newSTRef
```

Thus, the 'locality' guarantees are provided only by the source language
(Haskell in this case). The target language of the compiler (assembly language
with a custom runtime in GHC's case) does not contain any such checks or
provisions: there, any reference is mutable at any time. However, from the point
of view of a Haskell developer, this poses no problems, as the compiler ensures
that the issues of 'global' mutation cannot arise in any program that
typechecks. This is similar to the way Rust handles lifetimes and mutation:
while arbitrary mutation and aliasing are possible in whatever Rust compiles to,
the Rust language itself prevents issues with these by refusing to compile
problems which could be vulnerable to such problematic behaviour.

From the point of view of UPLC, it would not be difficult to construct some
datatype such as

```haskell
newtype MutRef a = MutRef (IORef a)
```

which could then be added to the Plutus default universe fairly easily. However,
the issue with this is that UPLC is a target language, and lacks the type system
required to ensure 'locality' of mutation. Indeed, the _only_ way mutability
could be made available at the level of UPLC is similar to how it is made
available in other onchain languages: through some form of implicitly-mutable
reference. Thus, it would be up to the frameworks (such as Plutarch) to ensure
'locality' guarantees were maintained.

This is severely problematic, as UPLC's immutable design exists to ensure that
certain guarantees of the entire Cardano blockchain are not broken. While it
might be possible to adjust or redefine these guarantees in the presence of
arbitrary global mutation, this represents such a radical change to the entire
ecosystem that this change is not practical, or more likely, even possible at
all. Despite the significant benefits that could come from allowing mutability
into UPLC, we believe that the trade-offs are so severe as to make it not worth
it.

## Better arrays

The third option for modifying UPLC to support parametric onchain verification
is to improve the existing API provided for arrays onchain.

At present, UPLC supports the notion of an array type, together with several
basic operations for retrieving the length of an array, converting an array into
a builtin list with the same data, and indexing of an array by a position. These
are described in more detail in [CIP-138][CIP-138]. This API is currently
supported by (at least) Plutarch and Plinth, to differing degrees of usefulness,
but ultimately, these basic operations define everything that UPLC can do with
arrays. This means that, at least in theory, UPLC now has the ability to handle
arrays, like basically every other onchain language outside of Cardano.

This is potentially of relevance to us, as many computations involved in
Grumplestiltskin have a natural representation as arrays:

- Second-degree field extensions are pairs.
- Elliptic curve points (especially projectively represented) naturally resemble
  arrays.
- Many computations involve intermediate values that could be stored in arrays.
- Several computations involve what amount to array reductions.

Unsurprisingly, all implementations of similar primitives to Grumplestiltskin in
other onchain languages (including the Solidity implementation referenced
previously) make heavy use of arrays.

However, UPLC's API for arrays is deficient in the extreme by comparison to its
peers, especially for our use case. In particular, all of the following are
currently essentially not possible in anything like an efficient manner, if at
all:

1. Constructing an array at runtime. CIP-138 first requires us to construct a
   list, then convert it to an array: this introduces $O(n)$ overhead in both
   time and space that is basically not avoidable. While we can cheaply 'lift'
   array _constants_, this is not particularly helpful in this context.
2. Updating an array. The only method currently possible involves first
   converting the array to a list via a manual loop, updating the list so
   produced, then converting back to an array again. This has the same $O(n)$
   overhead previously described, but then magnified by a factor proportionate
   the length of the dependency chain of updates, making it even more
   impractical.
3. Slicing or copying arrays. The only way to construct array slices requires a
   wrapper type with redundant information, and the only copying operation
   requires a list roundtrip and a manual traversal.

No other language, or library, onchain or otherwise, requires this much added
performance penalty or syntactic clutter to perform any of these operations.
Atop of this unacceptable performance penalty, there is also a significant cost
of implementational noise. While these limitations can be worked around to some
degree (as Plutarch does), it is at the cost of significant added complexity for
either the developer, the framework, or both. Given the sheer ubiquity of
arrays, both in the way implementations are described and actually implemented,
in a breadth of domains and languages, most developers are familiar with them,
and have certain expectations of how they 'should' work. CIP-138 makes these
assumptions range from useless to wrong, unless significant efforts are taken to
'paper over' these problems in a highly ad-hoc manner. In some sense, this is
the same issue as indirect representations (and Boehm-Berrarducci forms) but
writ much larger.

Furthermore, while UPLC's functional nature complicates its story with regard to
arrays, CIP-138 by no means represents the state-of-the-art, or even what is
reasonably expected, in a pure functional language's handling of arrays. Indeed,
Haskell's `vector` and `massiv` libraries demonstrate just how much is possible
in a functional context with sufficient primitives for arrays. However, given
all the above limitations, it is unlikely any analog to these libraries, or even
most of their capabilities, can exist in present-day UPLC.

We believe that a more robust API for arrays in UPLC would allow us to resolve
the performance problems we have described in Milestone 3. To demonstrate why,
we provide the following example of point addition in Solidity (from the
[same source as previous][SOLIDITY]):

```solidity
/// @dev Adds two points (x1, y1, z1) and (x2, y2, z2).
/// @param _x1 coordinate x of P1
/// @param _y1 coordinate y of P1
/// @param _z1 coordinate z of P1
/// @param _x2 coordinate x of P2
/// @param _y2 coordinate y of P2
/// @param _z2 coordinate z of P2
/// @param _pp the modulus
/// @return (qx, qy, qz) P1+P2 in Jacobian
function jacAdd(
        uint256 _x1,
        uint256 _y1,
        uint256 _z1,
        uint256 _x2,
        uint256 _y2,
        uint256 _z2,
        uint256 _pp
    ) 
    internal pure 
    returns (uint256, uint256, uint256) 
{
    if (_x1 == 0 && _y1 == 0) return (_x2, _y2, _z2);
    if (_x2 == 0 && _y2 == 0) return (_x1, _y1, _z1);

    // We follow the equations described in https://pdfs.semanticscholar.org/5c64/29952e08025a9649c2b0ba32518e9a7fb5c2.pdf Section 5
    uint256[4] memory zs; // z1^2, z1^3, z2^2, z2^3
    zs[0] = mulmod(_z1, _z1, _pp);
    zs[1] = mulmod(_z1, zs[0], _pp);
    zs[2] = mulmod(_z2, _z2, _pp);
    zs[3] = mulmod(_z2, zs[2], _pp);

    // u1, s1, u2, s2
    zs = [
        mulmod(_x1, zs[2], _pp),
        mulmod(_y1, zs[3], _pp),
        mulmod(_x2, zs[0], _pp),
        mulmod(_y2, zs[1], _pp)
    ];

    // In case of zs[0] == zs[2] && zs[1] == zs[3], double function should be used
    if (zs[0] == zs[2] && zs[1] == zs[3]) revert BetterUseJacDouble();

    uint256[4] memory hr;
    //h
    hr[0] = addmod(zs[2], _pp - zs[0], _pp);
    //r
    hr[1] = addmod(zs[3], _pp - zs[1], _pp);
    //h^2
    hr[2] = mulmod(hr[0], hr[0], _pp);
    // h^3
    hr[3] = mulmod(hr[2], hr[0], _pp);
    // qx = -h^3  -2u1h^2+r^2
    uint256 qx = addmod(mulmod(hr[1], hr[1], _pp), _pp - hr[3], _pp);
    qx = addmod(qx, _pp - mulmod(2, mulmod(zs[0], hr[2], _pp), _pp), _pp);
    // qy = -s1*z1*h^3+r(u1*h^2 -x^3)
    uint256 qy = mulmod(
        hr[1],
        addmod(mulmod(zs[0], hr[2], _pp), _pp - qx, _pp),
        _pp
    );
    qy = addmod(qy, _pp - mulmod(zs[1], hr[3], _pp), _pp);
    // qz = h*z1*z2
    uint256 qz = mulmod(hr[0], mulmod(_z1, _z2, _pp), _pp);
    return (qx, qy, qz);
}
```

We once again observe the naturality and parsimoniousness of this
implementation. This is made possible in no small part by the use of arrays: the
referenced implementation is described in these terms, and multiple array
operations are used here, ranging from accumulation, to scatter-gather, 'point'
updates and zipping. Furthermore, although the implementation itself does not do
this, it's clear to see that the points being added can be represented as arrays
themselves, which would allow even more array operations to be used to drive the
computation. This can be extended easily to elliptic curves over higher-order
extensions: simply increase the dimensionality of the relevant arrays. All of
this is currently either impossible, or far too inefficient, in UPLC, which is
why we ultimately did not consider it: a better API for arrays could change
this.

In some sense, a better API for arrays in UPLC is a 'middle ground' between our
two other suggestions. Unlike call-by-need with sharing, there is a more direct,
and demonstrable, performance improvement in our specific case, as well as more
generally. Unlike mutability, we do not have to worry about ruining the
guarantees of UPLC and Cardano, as the arrays themselves can remain immutable,
with the more capable operations allowing us to simulate mutation in a
restricted way. Furthermore, well-selected improved array primitives could
enable frameworks that generate UPLC to provide higher-level, more natural array
capabilities to developers than is currently possible.

## Conclusion

Based on our experiences with Grumplestiltskin as a whole, and Milestone 3 more
specifically, we believe that the kind of capabilities we sought to implement
simply cannot be implemented in a way that would 'fit' on the Cardano chain at
present. This stems from limitations in the capabilities UPLC currently
provides, and cannot be avoided at present. This is in no way forced upon us by
the chain: as we have illustrated, [at least one other implementation][SOLIDITY]
in a different onchain language both exists and is usable to achieve similar
goals to the ones we had in Grumplestiltskin. The problem is not in the nature
of UPLC as an onchain language; rather, it lies within the specifics of UPLC as
a language per se.

We have provided three possible paths forward. Any of these individually have a
good possibility of improving the sort of performance problems we found. At the
same time, we believe that the call-by-need solution is too conservative, and
the mutability solution is too disruptive. We thus position the improvement of
the CIP-138 array API as the middle ground: powerful enough to solve our
problem, but not so powerful as to destroy other, unrelated, currently-stable
systems. We gave an example of what such an improvement could look like as part
of the [Better Arrays treasury proposal][BETTER_ARRAYS], and believe that such
an improvement would benefit not just Grumplestiltskin-like projects, but any
similar work, particularly relating to cryptographical primitives.

Ultimately, we believe that the performance problems discovered as part of
Milestone 3 are not specific to Grumplestiltskin, but emblematic of a wider
performance deficiency in UPLC by way of inadequate primitives. Thus, our
proposed solutions are not simply designed to address the problems of
Grumplestiltskin, but those of many other onchain projects, which are possibly
not even aware of this problem yet. While the specifics of any of these
solutions require discussion and decisions, we feel that they are both important
and essential for future projects targeting UPLC.

[^1]: Specifically indirect 'on the outside', i.e. `ID`.

[call-by-need]: https://en.wikipedia.org/wiki/Evaluation_strategy#Call_by_need
[bb]: okmij.org/ftp/tagless-final/course/Boehm-Berarducci.html
[lazy-functional-state-threads]: https://www.microsoft.com/en-us/research/wp-content/uploads/1994/06/lazy-functional-state-threads.pdf
[M3]: https://github.com/mlabs-haskell/grumplestiltskin/blob/milestone-3/documents/milestone-3/ZK_VERIFIER_PROTOTYPE.md
[SOLIDITY]: https://github.com/witnet/elliptic-curve-solidity/blob/master/contracts/EllipticCurve.sol#L364C1-L408C1
[VECTOR]: https://hackage-content.haskell.org/package/vector-0.13.2.0/docs/Data-Vector-Strict.html#v:update
[BETTER_ARRAYS]: https://hydra-voting.intersectmbo.org/votes/cardano-budget-2026/69fb2e7485ddd26899aaf1fe
[DEFUN-PUSH-ARRAYS]: https://dl.acm.org/doi/epdf/10.1145/2636228.2636231
[PLUTARCH]: https://github.com/Plutonomicon/plutarch-plutus/blob/master/Plutarch/Array.hs
[COSTING]: https://github.com/cardano-foundation/CIPs/blob/master/CPS-0029/README.md
[CIP-138]: https://github.com/cardano-foundation/CIPs/tree/master/CIP-0138
[pull-arrays-blog-post]: https://www.mlabs.city/blog/performance-pull-arrays-and-plutarch
[UPLC-Laziness]: https://github.com/user-attachments/files/26065364/lazy-delay-force.pdf
