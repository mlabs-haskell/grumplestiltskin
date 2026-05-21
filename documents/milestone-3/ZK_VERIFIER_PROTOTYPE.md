# ZK verifier prototype and outcomes

## Introduction 

We attempted to implement a BLS12-381 KZG proof verifier prototype using 
primitives which are parameterized by fields and curves, in the Plutarch eDSL 
for UPLC script generation, as required by Milestone 3. In order to implement 
a ZK proof verifier, we first had to design and implement representations of, 
and operations on, [finite field extensions](https://en.wikipedia.org/wiki/Field_extension), 
which can be found in the  `src/Grumplestiltskin/Degree2` directory. These primitives 
can support other curves, but the BLS12-381 curves were the choice for our 
prototype. As BLS12-381's `G2` curve is defined over a second-degree extension, 
and requires a bilinear pairing function, supporting operations over finite field 
extensions, and curves over these, is a necessary first step.

Unfortunately, we found that the performance of any implementation is too low to
be viable. These performance limitations are similar to those we found as part
of Milestone 2 work (as documented in the [Milestone 2
report](https://github.com/mlabs-haskell/grumplestiltskin/blob/master/documents/milestone-2/EC_IMPLEMENTATION.md#limitations-and-potential-improvements)), 
but even more severe: even simple test cases (such as basic group operations 
for curves) approached or exceeded the limits set by Cardano protocol
parameters. Furthermore, there is no clear way to avoid these problems given the
state of UPLC at the time of writing this report.

This report will explain the nature of the performance problems we encountered,
demonstrate exactly how severe these issues are, and demonstrate that no
alternative solution exists. As part of this, we will also describe our attempts
to implement second-degree finite field extensions, and curves over these.

## Goals and priorities 

Our primary goal for Milestone 3 was to implement a BLS12-381 KZG verifier,
using primitives defined in Grumplestiltskin, rather than the builtins onchain.
This choice was made to mirror the Milestone 4 implementation, as this would
give us both a correctness indicator and a performance benchmark.

A necessary part of this implementation would be support for second-degree
finite field extensions: the `G2` BLS12-381 curve is a second-degree extension.
Thus, our initial priority was supporting both second-degree field extensions,
and elliptic curves over these.

As indicated in the introduction, this rapidly proved unviable, in spite of our
attempts to implement them in multiple ways. While we could theoretically have
built an extremely inefficient verifier, it would have been unusable for any
realistic test cases. Thus, we instead chose to describe what performance
limitations we experienced, how we attempted (and failed) to overcome them, and
why there is no viable alternative given the current state of UPLC.

## Implementation

We will describe our implementation choices for both field extensions and curves
over these. We defined multiple implementations to both try and find one that
was sufficiently performant, and also to demonstrate which were better or worse
relative others.

### Definitions 

We distinguish between _direct_ and _indirect_ representations of computations
onchain. These, when 'executed', produce some result. A _direct_ representation
encodes the computation as a standard data type; an _indirect_ representation
instead encodes the computation in [continuation-passing style][cps]. This
approach is analogous to the [Milestone 2 alternatives][m2-alts] we had
considered previously.

To clarify the difference, consider the following two representations of
computations producing an element of a second-degree field extension:

```haskell
-- The direct representation, from GaloisDirect.hs
data PD2Intermediate (s :: S) = PD2Intermediate (Term s PInteger) (Term s PInteger)

-- The indirect representation, from Galois.hs 
newtype PD2Intermediate (s :: S)
    = PD2Intermediate
        (forall (r :: S -> Type). Term s (PNatural :--> PPositive :--> (PInteger :--> PInteger :--> r) :--> r))
```

We will occasionally refer to the indirect representation as a
_Boehm-Berrarducci form_. This form encodes a (positive) [algebraic data
type][adt] as a function that produces any result of the caller's choice. This
is primarily a method of eliminating intermediate values, which is why we made
use of it in our work here. For a full explanation of the Boehm-Berrarducci form
and its consequences, please see [this paper][oleg-bb].

We will refer to several specific Cardano blockchain configuration settings
throughout this report as the _Cardano protocol parameters_. Specifically, the
following are of interest:

* `exUnitSteps`: The maximum number of computational 'steps' that a
  script can perform before execution is forced to halt. We will refer to this
  as the _CPU budget_ or _CPU cost_ for brevity.
* `exUnitsMem`: The maximum memory units a script can use during its
  execution. We will refer to this as the _memory budget_ or the _memory cost_
  for brevity.
* `maxTxSize`: The maximum size of a single transaction. On the Cardano
  blockchain, scripts must be attached to a transaction, though some versions
  allow referencing a script from an earlier transaction. We will refer to this
  as the _script size limit_, although technically, the realistic limit for a
  single script is less than this.

We note that the CPU budget and the memory budget are not true measurements of
either execution time or memory use for a script. Rather, these are synthetic
values, designed to allow measuring the costs of running a script using a
uniform and deterministic method. For more details, please see [this
overview][plutus-cost-model].

We distinguish between two forms of representations of elliptic curve points. An _affine_
representation is conceptually a point in two-dimensional space, while a
_projective_ representation is a point in a higher-dimensional space. We
specifically note that in the affine representation, we cannot represent the
point at infinity directly, whereas in a projective representation, we can. All
representations we implemented (and will describe) are affine representations:
we will discuss the reasoning for our choice in subsequent sections.

### Types

In our work for Milestone 2, we implemented data types corresponding to the
following:

* A finite field element
* A computation which, when run, produces a finite field element, in a direct
  representation
* An elliptic curve point over finite field elements
* A computation which, when run, produces an elliptic curve point over finite
  field elements, in a direct representation

While we had considered indirect representations, we found that there was no
advantage even in theory: the intermediate values were not large enough. 

For this Milestone, we would additionally require the following data types:

* An element of a second-degree finite field extension
* A computation which, when run, produces an element of a second-degree finite
  field extension
* An elliptic curve point over second-degree finite field extension elements
* A computation which, when run, produces an elliptic curve point over
  second-degree finite field extension elements

Initially, we attempted to directly extend Milestone 2 work by using direct
representations for all the above. However, we found that this had unacceptably
bad performance. Thus, we decided to attempt the use of indirect representations
as well.

As indirect representations would provide no benefits for types _not_
representing computations, for second-degree field extension elements and
elliptic curve points over these, we implemented only a direct type: these are,
respectively `PD2Element` and `PEC2Point`. These can be found in the
`Degree2.Element` and `Degree2.AffinePoint` modules respectively.

For computations over these, we require two types conceptually:

* `PD2Intermediate`, for second-degree field extension elements; and
* `PEC2Intermediate`, for elliptic curves over these.

Each of these types can have either a direct or indirect representation, which
gives four possibilities:

* Direct `PEC2Intermediate` using direct `PD2Intermediate` (`DD`)
* Direct `PEC2Intermediate` using indirect `PD2Intermediate` (`DI`)
* Indirect `PEC2Intermediate` using direct `PD2Intermediate` (`ID`)
* Indirect `PEC2Intermediate` using indirect `PD2Intermediate` (`II`)

These can be found, respectively, in the `EllipticCurveDD`, `EllipticCurveDI`,
`EllipticCurveID` and `EllipticCurveII` modules in the
`src/Grumplestiltskin/Degree2` directory. 

For each of these representations, we also implemented the required group and
field operations. Notably, this meant an additional auxiliary value is required
(specifically, an [irreducible element][irreducible]) for field extensions and
also elliptic curves over these. For indirect representations, we were able to
use the Plutarch numerical hierarchy of type classes to implement this
functionality. We could not do this for direct representations for similar
reasons to the Milestone 2 implementation of elliptic curves, as these type
class methods do not allow passing of auxiliary values. Thus, we implemented
the same operations as regular functions.

For clarity, we provide the following table of equivalent operations. Some
operations use identical names regardless of representation.

| **Operation**  | Direct function name | Indirect function name |
|----------------|----------------------|------------------------|
| Field addition | `#+`                 | `#+`                   |
| Field multiplication | `pd2Times`     | `#*`                   |
| Field additive inverse | `pnegate`    | `pnegate`              |
| Field square           | `pd2Square`  | `pd2Square`            |
| Field division         | `pd2Divide`  | `pd2Divide`            |
| Field exponentiation | `pd2Pow`       | `pd2Pow`               |
| Group addition | `pec2Add`            | `#+`                   |
| Group doubling | `pec2Double`         | `pec2Double`           |
| Group inverse  | `pec2Negate`         | `pnegate`              |
| Group scaling  | `pec2Scale`          | `pscaleInteger`        |

We note that, as the Plutarch numerical hierarchy has several additive scaling
methods, `pscalePositive` and `pscaleNatural` were also implemented for the
representations that allow them.

## Benchmarks 

We implemented a benchmark suite to compare performance tradeoffs between the
different representation choices for second-degree finite field extensions and
elliptic curves over these. The implementations of these benchmarks can be found
in `test/extension-ec/Main.hs`, and the cached golden files noting their
performance can be found in `goldens/extension-ec.bench.golden`. 

We separated the benchmarks into several distinct groups, all of which benchmark
the same operation or procedure using different representations of second-degree
finite field extensions (or curves over these). The key groups are as follows:

* Addition
* Negation
* Scaling
* Scale-add

The benchmarks in each group were implemented identically, with the only
difference being the choice of direct or indirect representation (and the use of
corresponding functions). Unfortunately, due to a quirk of the Plutarch golden
testing framework, not all the results could be run with the same data: we will
discuss the reasons for this shortly.

To help demonstrate the efficiency (or rather, lack of efficiency) of each of
these operations, we will make frequent reference to the CPU budget, the memory
budget and the script size limit. The values for these, given by the current
[genesis files](https://book.world.dev.cardano.org/env-mainnet.html), are as
follows: 

| **CPU limit** | **Memory limit** | **Script size limit (bytes)** | 
|--- | --- | --- | 
|10,000,000,000 |10,000,000 | 16,384 | 

Where appropriate, we indicate what percentage of these limits any given
benchmark required.

### Benchmark data

Our benchmarks make use of a shared set of values, originating from a fixed set
of constants. Specifically, we use two BLS12-381 G2 curve points. The first of
these is defined on the basis of the following four constants:

```haskell
validX1 :: Natural
validX1 = 0x24aa2b2_f08f0a91_26080527_2dc51051_c6e47ad4_fa403b02_b4510b64_7ae3d177_0bac0326_a805bbef_d48056c8_c121bdb8

validX2 :: Natural
validX2 = 0xce5d527_727d6e11_8cc9cdc6_da2e351a_adfd9baa_8cbdd3a7_6d429a69_5160d12c_923ac9cc_3baca289_e1935486_08b82801

validY1 :: Natural
validY1 = 0x13e02b60_52719f60_7dacd3a0_88274f65_596bd0d0_9920b61a_b5da61bb_dc7f5049_334cf112_13945d57_e5ac7d05_5d042b7e

validY2 :: Natural
validY2 = 0x606c4a0_2ea734cc_32acd2b0_2bc28b99_cb3e287e_85a763af_267492ab_572e99ab_3f370d27_5cec1da1_aaa9075f_f05f79be

blsC1 :: forall (s :: S). Term s PEC2Point
blsC1 = evalTerm' NoTracing (pec2FromElems (pconstant . mkBLS validX1 $ validY1) (pconstant . mkBLS validX2 $ validY2))
```

The second is produced by scaling `blsC1` by an integer scalar of `3`. As the
implementation will appear differently based on which representation we are
using, we provide only the `DD` example below:

```haskell
blsC2DD :: forall (s :: S). Term s DD.PEC2Intermediate
blsC2DD = evalTerm' NoTracing (DD.pec2ToIntermediate . DD.pec2FromIntermediate pblsOrder $ DD.pec2Scale pblsOrder validRSquared validCurveA blsC1DD 3)
```

In both cases, we make use of `evalTerm'` to ensure that the cost of
constructing these points is not factored into the benchmarks.  

### Addition

Our first group of benchmarks measures addition of elliptic curve points over
second-degree finite field extensions. Each of the benchmarks measures the
addition of the two point constants described previously, using different
representations.

The results were as follows:

| **Operation** | **Representation** | **CPU cost (% of limit)**  | **Memory cost (% of limit)** | **Script size (% of limit)** | **Code** | 
|---|---|---|---|---|---|
| `#+` | `II` | 100,291,545 (1%) | 104,792 (1%) | 2,547 (15.5%)| `blsC1II #+ blsC2II` |
| `#+` | `ID` | 48,214,005 (0.48%)  | 48,183 (0.5%) | 2,440 (14.9%) | `blsC1ID #+ blsC2ID` |
| `pec2Add` | `DD` | 49,275,939 (0.49%)  | 51,431 (0.51%) | 3,332 (20.3%) | `DD.pec2Add pblsOrder validRSquared validCurveA blsC1DD blsC2DD` |
| `pec2Add` | `DI` | 101,049,479 (1.01%)  | 106,140 (1.1%) | 3,093 (18.9%) | `DI.pec2Add pblsOrder (punsafeCoerce validRSquared) validCurveA blsC1DI blsC2DI` |

These benchmarks are directly comparable, as their inputs were identical. These
results reveal a pattern which will occur across all the benchmarks: direct
'inner' (that is, `ID` or `DD`) representations are much more efficient in terms
of CPU and memory usage. In this case, this is almost a factor of two
improvement. Direct 'outer' representations instead lead to noticeably larger
script sizes. We also observe that the choice of direct or indirect 'outer'
representation seems to make little difference in terms of CPU or memory cost.

Overall, `DI` is the worst representation overall, while `ID` is
the best. At the same time, script sizes are all surprisingly large, given how
fundamental this operation is.

### Negation

Our second group measures negation of elliptic curve points over second-degree
finite field extensions. Each of the benchmarks specifically measures the
negation of the `blsC1` point described previously, in the appropriate
representation.

The results were as follows:

| **Operation** | **Representation** | **CPU cost (% of limit)**  | **Memory cost (% of limit)** | **Script size (% of limit)** | **Code** | 
|---|---|---|---|---|---|
| `pnegate` | `II` | 2,202,412 (0.02%) | 11,538 (0.12%) | 556 (3.4%) | `pnegate # blsC1II` |
| `pnegate` | `ID` | 1,978,412 (0.019%) | 10,138 (0.1%) | 544 (3.3%) | `pnegate # blsC1ID` | 
| `pec2Negate` | `DD` | 2,198,108 (0.022%) | 10,462 (0.1%) | 666 (4%) | `DD.pec2Negate blsC1DD` | 
| `pec2Negate` | `DI` | 2,486,108 (0.024%) | 12,262 (0.12%) | 904 (5.5%) | `DI.pec2Negate blsC1DI` | 

As previously, we observe that direct 'outer' representations lead to larger
script sizes. However, the differences between the implementations are minor:
all lead to reasonably efficient code. Overall, `DI` is once again the worst
representation, while `ID` is the best.

### Scaling 

Our third group concerns elliptic curve point scaling, which is effectively
repeated addition. Initially, we attempted to scale the `blsC1` point (in the
appropriate representation) by an integer scalar of `32`. However, only the `II`
and `ID` representations could run and still fit into the limits described
previously. This poses a problem with Plutarch's benchmarking framework, as it
is designed to simulate the onchain limits exactly. Thus, these benchmarks
couldn't even report a result. In order to produce values at all, we were forced
to reduce the integer scalar for the `DD` and `DI` cases to `4`.

This means the following results are not directly comparable. As resolving this
problem would require modifying Plutarch itself, we did not attempt to do this,
instead presenting the results as they are here.

| **Operation** | **Representation** | **CPU cost (% of limit)**  | **Memory cost (% of limit)** | **Script size (% of limit)** | **Code** | 
|---|---|---|---|---|---|
|`pscaleInteger` | `II` | 610,966,110 (6.1%) | 579,291 (5.8%) | 1,925 (11.7%) | `pscaleInteger blsC1II 32` |
|`pscaleInteger` | `ID` | 321,525,626 (3.2%)| 291,775 (2.9%) | 1,789 (10.9%) | `pscalePositive blsC1ID (punsafeCoerce @_ @PInteger 32)` | 
|`pec2Scale` | `DD` | 1,053,146,819 (10.5%) | 132,257 (1.3%) | 2,651 (16.2%) | `DD.pec2Scale pblsOrder validRSquared validCurveA blsC1DD 4` | 
|`pec2Scale` | `DI` | 1,929,108,917 (19.3%)| 660,473 (6.6%) | 2,962 (18%) | `DI.pec2Scale pblsOrder (punsafeCoerce validRSquared) validCurveA blsC1DI 4` | 

We note that, as our scaling implementation (in all cases) uses [exponentiation
by squaring][exponentiation-by-squaring], the `pec2Scale` benchmarks are likely
to be at least three times worse than the figures given above for CPU and memory
cost. However, even without this, we can see that `DD` and `DI` cases display
severe performance degradation compared to the `II` and `ID` cases. Furthermore,
we note that indirect 'inner' representations always lead to worse memory usage.
Finally, as previously, direct 'outer' representations lead to significantly
larger script sizes.

At the same time, we can see that all of these operations require quite large
portions of the script size budget: even the smallest is over 10%. Given that
this is a single operation, intended to be part of a larger script, over a small
constant, shows that it's not realistic for use on the chain. Furthermore, we
cannot simultaneously obtain the best CPU cost and the best memory cost no
matter our representation choices. This is different from the prior cases where
a clear 'best' option exists.

### Scale-Add 

Our final group concerns a compound operation that scales the `blsC1` point (in
the appropriate representation) by the scalar `2`, then adds it to another copy
of `blsC1`. 

This 'scale-add' operation was chosen for two reasons. Firstly, it illustrates
the benefits of indirect representations (which we will discuss further in a
later section). Secondly, it is useful for ascertaining the viability of an
onchain implementation, as this combination of operations is central to the
bilinear pairing for the BLS12-381 curves (as per [this source, page
79][pairings-for-beginners]). We note that in practice, the number of such
operations will depend on the commitment being verified, but any realistic case
would require much more than one such operation, and the constants involved will
be much larger than `2`.

We had to choose such a small integer to ensure benchmark comparability:
demonstrating any benefit to indirect representation would be impossible
otherwise. Any larger constant would cause the `DD` and `DI` benchmarks to fail
to run, for reasons similar to those discussed for the scaling benchmarks given
previously. Furthermore, even the `ID` and `II` benchmarks cannot run with
constants larger than about `1000`.

The results are as follows:

| **Operation** | **Representation** | **CPU cost (% of limit)**  | **Memory cost (% of limit)** | **Script size (% of limit)** | **Code** | 
| --- | --- | --- | --- | --- | --- | 
| scale-add | `II` | 205,141,864 (2.05%) | 223,648 (2.24%) | 3,414 (20.8%) | `blsC1II #+ pscaleInteger blsC1II 2` |
| scale-add | `ID` | 99,850,088 (1%) | 110,316 (1.1%) | 3,184 (19.4%) | `blsC1ID #+ pscaleInteger blsC1ID 2` |
| scale-add | `DD` | 579,644,274 (5.8%) | 120,400 (1.2%) | 5,634 (34.4%) | `DD.pec2Add pblsOrder validRSquared validCurveA blsC1DD (DD.pec2Scale pblsOrder validRSquared validCurveA blsC1DD 2)` | 
| scale-add | `DI` | 1,127,817,205 (11.3%) | 513,753 (5.14%) | 5,909 (36%) | `DI.pec2Add pblsOrder (punsafeCoerce validRSquared) validCurveA blsC1DI (DI.pec2Scale pblsOrder (punsafeCoerce validRSquared) validCurveA blsC1DI 2)` | 

We can immediately see the issue here: even at such small scales, these
operations require between 20 and 30% of the entire script size limit. When
combined with the observations of resource exhaustion with larger (but not
large) constants, this clearly demonstrates the unviability of any of these
choices in practice. Other observations are consistent with previous benchmarks.

### Discussion 

The benchmarks reveal a clear pattern: with the exception of the negation
operation, even the most efficient choices of representation still fall
considerably short of the requirements needed to be practically usable onchain.
This is particularly apparent for script sizes, but even when the CPU and memory
costs are reasonable, we note that the benchmarks are for relatively simple
computations. Any practical verifier would require much larger arguments, and
many more computations, which would be intolerably resource-intensive. 

To see this inefficiency more clearly, we can use the [prototype KZG
verification function][m4-prototype] as a reference. Specifically, we note the
following:

* Prior to computing the pairing, we must perform two scaling operations over the
  value `r`. This value, designed to represent a 'challenge' from the verifier,
  would need to be fairly random to be useful. This will mean that its magnitude
  would be large. Given that our most efficient representation can only handle
  constants around `1000`, this already suggests that this is not possible in
  practice.
* The script sizes of all basic operations is unrealistically high. For example,
  even the most efficient addition of two points requires 15% of the script size
  budget. We also note that the size budget is for a _transaction_, rather than
  a single script, which means that any verifier would need to leave budget
  available for other computations.
* An implementation of the required bilinear pairing would be impossible in
  practice, given the costs of even a single scale-and-add.

These problems are not new or unexpected: we encountered similar issues even
during the development of Milestone 2. However, in that context, the simpler
data we were working with allowed some possibility of success. Over
second-degree field extensions, these existing problems magnify significantly.
Indeed, had we used the same strategy as we did for Milestone 2, our
implementation would be even more unviable, as direct representations performed
the worst in all of our benchmarks.

## Causes of performance breakdown

Fundamentally, the poor performance demonstrated by our benchmarks stems from
two specific issues. The first, exhibited quite strongly by the direct
representation, is the large number of intermediate values that must be produced
for almost all computations. The indirect representation, specifically chosen to
address this issue, does do so, but in return, leads to a second issue:
over-evaluation by necessity. Both of these performance issues were already on
display for the code produced for Milestone 2. However, due to the larger data
requirements of second-degree field extensions (and curves over these), these
issues magnify significantly. 

At the heart of both problems is a quirk of the affine representation of curve
points. As the point at infinity cannot be represented as a two-dimensional
coordinate in this system, we must use a sum type as the representation. UPLC
can represent sum types in two ways:

* Using the `Constr` data constructor of `Data` with different tags; and
* Using the builtin SOP support.

Every time such a value is constructed, regardless of which of these
representations we choose, we must pay a cost. If we have 'combination'
operations, these costs 'add up', even though we never require the intermediate
values produced this way. A good example of this is elliptic curve point
scaling: as we use exponentiation by squaring, we _must_ produce (and pay for!)
$\log(n)$ points, even though we only ever need the last one. Second-degree
field extensions make this problem far worse. As we are operating on pairs of
finite field elements, every operation over finite fields must construct more
intermediate values (and larger intermediate values), which has a knock-on
effect for elliptic curve operations over these. As an example, consider field
multiplication:

* For finite field elements, this is a single builtin integer multiplication;
* For second-degree extensions, this is _five_ builtin integer multiplications,
  and two builtin integer additions.

Furthermore, second-degree field extensions must be represented a composite type
(essentially a pair), which means the costs of construction of intermediates
also magnify relative regular finite field elements, which can be represented as
builtin integers. All of this 'intermediate value pressure' combines to produce
the results we see both in Milestone 2 and here.

The only way to evade this is to use Boehm-Berrarducci encodings, which we chose
as the indirect representation. This is based on the capability of
Boehm-Berrarducci encodings to naturally 'fuse away' intermediate values: as any
such encoding is just a function, we do not need to 'materialize' any values
until the point at which we demand a result, which would be of a different type
than whatever the encoding is representing. We can indeed see from our
benchmarks that this is a worthwhile improvement in this case. This is in
contrast to Milestone 2, where such a representation was considered, but
ultimately deemed not to be worthwhile, as the intermediate values were much
smaller and fewer in number.

At the same time, the indirect representation suffers from the same kind of
issue we identified in Milestone 2: inherent over-evaluation. This stems from
the same cause [identified previously][m2-alts], which is again caused by the
use of sum types to represent affine curve points. Briefly, the issue stems from
the nature of Boehm-Berrarducci encodings as _functions_: for sum types
specifically, this means that a pattern match is an evaluation. For elliptic
curve addition, we must first verify whether either argument is the point at
infinity. Doing this _forces_ us to evaluate _both_ encodings, even if we don't
need to. As described in Milestone 2, this is unavoidable, as UPLC has strict
semantics, without any ability to cache already-evaluated results. This
over-evaluation is _especially_ impactful on the performance of elliptic curve
scaling, as we have to perform potentially many curve point additions using the
same argument repeatedly. Our benchmarks clearly demonstrate this problem: even
for small scalars, the costs become intolerable quickly.

Ultimately, we can see that within the limits placed on us by UPLC as it
currently stands, we cannot avoid these issues while still making use of an
affine representation for curve points. Any attempt to address one problem
inherently produces the other: at best, we can only trade these problems _for_
each other, not even _against_ each other. Thus, we are forced to conclude that
any attempt to have curves over second-order finite field extensions simply
isn't practical as it stands, thereby making any verifier requiring them
unusable as well.

## Alternatives considered

A natural question from the prior discussion is whether we can avoid using
affine encodings, and their inherent need for sum types. Indeed, various
projective encodings are already in use for many implementations of elliptic
curve operations, any of which are capable of representing the point at infinity
directly. This would allow us to avoid the use of sum types altogether, which
would potentially eliminate the over-evaluation problem of the indirect
representation. 

However, any projective representation, by necessity, increases the amount of
work required to perform any operation on elliptic curves relative the affine
representation, particularly in UPLC. This stems from a quirk of UPLC that (to
our knowledge) exists in no other onchain language: finding a modular
multiplicative inverse is a cheap operation. Projective encodings were motivated
largely by the need to avoid modular multiplicative inverse-finding, as this is
an expensive operation requiring the use of the [extended Euclidean
algorithm][extended-euclid]. Avoiding this by replacing it with a fixed
additional number of other operations is worthwhile in this case, but not in
ours: we lose far more than we gain. This tradeoff, already considered in
[Milestone 2][m2-alts], remains just as unviable as it was for our prior work.

## Conclusion

While our work from Milestone 2 that implemented elliptic curves over finite
field elements was promising, any attempt we could make to extend it to
second-degree field extensions runs into intractable performance issues. These
issues, already identified as part of our Milestone 2 work, hit even harder
here: all operations cost more, all intermediate values are larger, and all
benchmarks are thus correspondingly worse. Thus, any attempt to implement a
verifier are doomed to failure and impracticality, even in the best possible
choice of implementation.

Furthermore, these problems are unavoidable due to the limited capabilities of
UPLC that we are given to work with. No change of representation, or clever
implementation strategy, will eliminate the problems for performance that we
have observed and demonstrated through our benchmarks. These are not limitations
in our implementational capabilities, or Plutarch: they stem from UPLC itself,
and the specific set of tools it gives us. Without change to UPLC, these
performance issues _must_ exist. Thus, as it stands, implementing the goal of
this Milestone, or indeed, the remainder of the Grumplestiltskin project, is not
possible.

Lastly, these problems are not only inherent to UPLC, they are also unique to
it. The techniques that we had to employ, both for this Milestone and Milestone
2, are unusual by the standards of onchain languages (or indeed, programming
languages in general). This does not stem from UPLC's functional nature, nor
from its constrained budgets _inherently_: they are implementational choices
specific to it, shared by no other language we know of. This means that the
performance problems we have identified are not unique to Grumplestiltskin, but
_must_ affect other work that has similar needs. We believe this extends to all
code of a cryptographical nature, but likely far beyond that as well. Thus,
addressing the root causes of these performance problems is necessary, but
cannot be done within the scope of this project.

[cps]: https://en.wikipedia.org/wiki/Continuation-passing_style
[m2-alts]: https://github.com/mlabs-haskell/grumplestiltskin/blob/master/documents/milestone-2/EC_IMPLEMENTATION.md#representation-of-elliptic-curve-points
[adt]: https://en.wikipedia.org/wiki/Algebraic_data_type
[oleg-bb]: https://okmij.org/ftp/tagless-final/course/Boehm-Berarducci.html
[plutus-cost-model]: https://github.com/IntersectMBO/plutus/blob/master/doc/cost-model-overview/cost-model-overview.pdf
[irreducible]: https://en.wikipedia.org/wiki/Irreducible_element
[exponentiation-by-squaring]: https://en.wikipedia.org/wiki/Exponentiation_by_squaring
[pairings-for-beginners]: https://static1.squarespace.com/static/5fdbb09f31d71c1227082339/t/5ff394720493bd28278889c6/1609798774687/PairingsForBeginners.pdf
[m4-prototype]: https://github.com/mlabs-haskell/grumplestiltskin/blob/sean/m4-report/src/Grumplestiltskin/Verify.hs
[extended-euclid]: https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm
