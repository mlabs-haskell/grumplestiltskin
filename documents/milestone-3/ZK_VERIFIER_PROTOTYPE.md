# ZK Verifier Prototype 

## Introduction 
We attempted to implement a BLS12-381 KZG proof verifier prototype using primitives which are parameterized by fields and curves, in the Plutarch eDSL for UPLC script generation, as required by Milestone 3. In order to implement a ZK proof verifier, we first had to design and implement representations of, and operations on, finite field extensions, which can be found in the  `src/Grumplestiltskin/Degree2` directory. (These primitives can support other curves, but BLS was the target for our prototype.) Because verification in a BLS12-381 context requires implementing a pairing function which accepts a point on the `G2` curve, and because the `G2` curve is a curve over 

Unfortunately, we ran into intractable problems during this step that made it clear to us that a BLS verifier built on top of these primitives is not viable. The limitations we discovered in M2 proved even more limiting in the case of operations over second degree field extensions, such that even simple test cases (i.e. of the primitive operations, not of verification) approached or exceeded limits set but Cardano protocol parameters. The current state of UPLC, therefore, forces us into a dilemma: Representations of field extensions which lead to acceptable script sizes incur extreme CPU and memory costs, whereas representations that lead to acceptable CPU and memory costs produce script sizes which reach or exceed the limits even in artificially small and simple test cases.

We believe that our results demonstrate that no implementation could satisfy the performance requirements necessary for on-chain use, and that our failure here is the result of a true dilemma.

Our aim in this report is to explain why field extensions are necessary for parametric proof verification, explain the the multiple ways we represented field extensions, provide evidence that none of our representations are feasible for onchain verification given current or foreseeable protocol parameters, and finally, to make the case that any projective representation - the only alternative to our affine approach here - can do no better (and will almost certainly do much worse).

## Goals and Priorities 

Our primary goal for the milestone was to implement a BLS12-381 KZG verifier prototype using parametric primitives. While we could have chosen other curves in principle, in practice BLS was the only sensible choice since UPLC primitives support that curve, which allows us to compare our results here with the "builtin" implementation we constructed for Milestone 4. 

Because the G2 curve is a second degree extension of the G1 curve, and because a pairing function over these curves is an essential component of any verifier, implementing parametric primitives for second degree field extensions and curves over such extensions is a necessary first step towards implementing a verifier prototype. To that end, our initial goal and first priority was to implement parametric primitives for second degree field extensions. 

As indicated in the introduction, we ran into intractable performance problems when attempting to implement these primitives. While it would have been conceptually possible to build an extremely inefficient verifier on top of our primitives, doing so would have no purpose because our preliminary results clearly demonstrate a severe performance degradation in the primitive operations on small and simple test cases. 

In the following sections, we will explain the various ways in which we attempted to represent second-degree field extensions, curves over those extensions, and primitive operations over both, and then provide evidence which we believe demonstrates (with a high degree of certainty) that neither our implementation nor any other can yield a viable onchain implementation of second degree field extensions and operations over them. 

## Implementation of Second Degree Field Extensions 

### Definitions 

Throughout the remainder of the report we will employ several technical concepts which may not be familiar to most readers. Therefore, we will define them here: 

1. We distinguish between *direct* and *indirect* representations of _computations_ that, when run, produce a result. The *direct* representation encodes the computation as a straightforward datatype (a product or sum), whereas the *indirect* representation encodes the computation in continuation-passing style. An example makes the difference clear - these are the two representations of `PD2Intermediate`, which is a computation that returns a second degree field extension element when run: 

```haskell
-- The direct representation, from GaloisDirect.hs
data PD2Intermediate (s :: S) = PD2Intermediate (Term s PInteger) (Term s PInteger)

-- The indirect representation, from Galois.hs 
newtype PD2Intermediate (s :: S)
    = PD2Intermediate
        (forall (r :: S -> Type). Term s (PNatural :--> PPositive :--> (PInteger :--> PInteger :--> r) :--> r))
```

2. We will occasionally refer to the encoding style of the indirect representation as a *Boehm-Berarducci form* (or a **BB form** for short). The BB encodes a datatype as a function. In the context of our work here, the primary benefit is that it should improve performance by fusing away intermediary computations. A thorough explanation of BB forms would be out of place here, however the reader can refer to [this excellent paper](LINK TO OLEG'S PAPER) which explains in great detail the construction, purpose, and benefits of BB forms. 

3. We will often refer to the *Cardano protocol parameters*, which are configuration settings for the Cardano blockchain. For us, the most relevant parameters are:
  - *exUnitsSteps*: A value which represents the maximum number of computational steps a script can perform before execution is halted. This does not correspond directly to CPU operations on hardware - it is a synthetic value that is based on a set of costing parameters for language constructs and builtin functions - but because it is analogous to CPU usage in other contexts, we will sometimes refer to it as the "CPU budget" or "CPU cost" to distinguish it from the other costs. 
  - *exUnitsMem*: A value that represents the maximum amount of memory a script can consume. 
  - *maxTxSize*: A value that represents the maximum size of a single transaction. On the Cardano blockchain, scripts must be attached to a transaction. In some protocol versions they may be referenced by subsequent transactions, but must be attached at least once. We will occasionally refer to this as the *script size limit*, even though the actual maximum size for a Plutus script is strictly (slightly) smaller than this, because the transaction must contain elements other than the script itself. For our purposes the difference is largely immaterial, for reasons which will become obvious shortly. 
  
4. We distinguish (generally) between *affine* and *projective* representations of curve points. An affine representation represents points as coordinate pairs in 2 dimensional space. Non-affine representations (of which there are several) represent points as sets of coordinates in 3 or more dimensions. All of the representations we implemented, whether direct or indirect, are affine representations. 
  
### Types

In our Milestone 2 work, we implemented datatypes and group operations over elliptic curves using two distinct representations: A direct (i.e. SOP-encoded) representation, and an indirect (i.e. Boehm-Berarducci form) representation. Group operations in M2 were defined over a type (`PECIntermediatePoint`) that represents an intermediate computation on points. (See the Milestone 2 report for details.) 

In our Milestone 3 work, we continued along this path when designing representations and operations over field extensions. However, since we are now dealing with elements of field extensions _and_ curve points, we must implement two different kinds of intermediate computations: 

  - `PD2Intermediate`, which represents a computation that, when run, produces an element of a second degree field extension
  - `PEC2Intermediate`, which represents a computation that, when run, produces a point on some elliptic curve
  
Each of these types can, in a manner following M2, be represented in a direct or indirect way. The indirect and direct representations of `PD2Intermediate` can be found, respectively, in the `Grumplestiltskin.Degree2.Galois` and `Grumplestiltskin.Degree2.GaloisDirect` modules.  

Because `PEC2Intermediate` can itself be represented directly or indirectly, and because it must refer to `PD2Intermediate` results (which may be represented directly or indirectly), there are four possible variants of `PEC2Intermediate`: 
  1. Direct `PEC2Intermediate` using direct `PD2Intermediate` (`DD`)
  2. Direct `PEC2Intermediate` using indirect `PD2Intermediate` (`DI`)
  3. Indirect `PEC2Intermediate` using direct `PD2Intermediate` (`ID`)
  4. Indirect `PEC2Intermediate` using indirect `PD2Intermediate` (`II`)
  
These can be found, respectively, in the `EllipticCurveDD, EllipticCurveDI, EllipticCurveID, EllipticCurveII` modules in the `src/Grumplestiltskin/Degree2` directory. 

The "result types" of the intermediate computations, `PD2Element` and `PEC2Point` (which is comprised of `PD2Element`s) have only one representation (the direct one), and can be found in `Degree2.Element` and `Degree2.AffinePoint` respectively, along with their Haskell-level counterparts. 

## Benchmarks 

We implemented a benchmark suite to compare the performance tradeoffs between various ways we represented field extensions and their operations. Each benchmark test here implements a small computation over elliptic curves using the designated representation (e.g. `DI` means a direct `PEC2Intermediate` with an indirect `PD2Intermediate`, and so on). 

The implementation of the benchmarks can be found in `test/extension-ec/Main.hs`, and the cached golden results can be found in `goldens/extension-ec.bench.golden`. There are other benchmarks and tests in our test directory, but only these are particularly pertinent for this report. Wherever possible, we use pre-evaluated terms to minimize the amount of onchain computation. 

The benchmarks can be conceptually divided into several distinct groups, which all benchmark the same operation or procedure using different representations (i.e. varying the direct/indirect representations of `PE2CIntermediate` and `PD2Intermediate`). While we implemented additional benchmarks groups, those necessary to make our case here are: 
  1. Addition Operations 
  2. Negation Operations 
  3. Scaling Operations 
  4. Scale-add computations 

For reasons related to implementation details of the Plutarch eDSL, some operations are implemented as standalone functions while others are implemented as typeclass methods. We preferred the type class method implementation where possible, however it is not possible to implement instances of the relevant type classes using auxiliary data, which several representations require. Specifically, representations that use a direct `PEC2Intermediate` must make use of auxiliary data, so we cannot write a typeclass instance, and therefore must (e.g.) use a standalone `pec2Add` function instead of the typeclass method `#+` for addition. 

A quirk of the testing framework mandates that we produce _UPLC scripts which do not exceed protocol limits_, i.e., which stay under the aforementioned CPU and memory limits. There is no conceptual need for this, as the Cek machine that powers UPLC evaluation is capable of running with different limits or none at all, but this would require modifying the Plutarch golden testing infrastructure to implement, so we did not do so. This is important for understanding the benchmarks, because in several places we were forced to reduce the magnitude of certain input values for particular tests in order to stay within those limits. Readers should pay careful attention the explanatory comments before each table presenting the relevant benchmarks, since different entries may use different input values, and the results are not necessarily directly co-measurable. Obviously, representations which had to be scaled down significantly to fit within the limits even for simple test cases are unambiguously non-viable.

For the sake of clarity, it will help the reader to understand our naming scheme for the tests (which has been hinted at above). The code `DD` indicates a direct `PEC2Intermediate` with a direct `PD2Intermediate`, `II` indicates an indirect `PEC2Intermediate` with a direct `PD2Intermediate`, and so on. The full list of shorthand codes can be found in the previous section. 

Finally, since we will refer below (where appropriate) to the percentage of the total budget (for CPU, memory, and script size) each benchmark consumes, it may be useful for readers to review those budgetary limits. We note in passing that the CPU and memory budgets are, at least to some extent, "synthetic", in that they are based on a cost model and not on actual hardware performance (i.e. the numbers do not necessarily correspond *directly* to any kind of hardware operations). Script size is denominated in bytes, and _does_ directly indicate the "physical" size of a script. All values were retrieved from [current genesis files](https://book.world.dev.cardano.org/env-mainnet.html)

| CPU Limit | Memory Limit | Script Size Limit (Bytes) | 
|--- | --- | --- | 
|10,000,000,000 |10,000,000 | 16,384 | 

### Addition

The first group of benchmarks concerns addition of points on a curve over the second degree extension of a field. Each of the tests consists of a simple addition of two such points, using a different combination of representations. Each of the tests consists in adding the same two points, which are represensented differently but constructed from the same source. In particular, the first point (`blsC1`) being added originates from: 

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

While the second point being added is produced by scaling `blsC1` by an integer scalar of `3`. The implementation of that scaling will look slightly different for each representation, but the `DD` case gives the general idea: 

```haskell
blsC2DD :: forall (s :: S). Term s DD.PEC2Intermediate
blsC2DD = evalTerm' NoTracing (DD.pec2ToIntermediate . DD.pec2FromIntermediate pblsOrder $ DD.pec2Scale pblsOrder validRSquared validCurveA blsC1DD 3)
```

We use `evalTerm'`, which pre-evaluates a term, everywhere possible in order to isolate the budgetary cost of the operations being benchmarked. Here, we use it because `blsC2DD` is effectively a constant for testing purposes, and the cost of constructing it should not figure into the benchmark results. 

The results:

| Operation | Representation | CPU Cost (% Max Budget)  | Memory Cost (% Max Budget) | Script Size (% Max Budget) | Code 
|---|---|---|---|---|---|
| #+ | II | 100291545 (1%) | 104792 (1%) | 2547 (15.5%)| `blsC1II #+ blsC2II` |
| #+ | ID | 48214005 (0.48%)  | 48183 (0.5%) | 2440 (14.9%) | `blsC1ID #+ blsC2ID` |
| pec2Add | DD | 49275939 (0.49%)  | 51431 (0.51%) | 3332 (20.3%) | `DD.pec2Add pblsOrder validRSquared validCurveA blsC1DD blsC2DD` |
| pec2Add | DI | 101049479 (1.01%)  | 106140 (1.1%) | 3093 (18.9%) | `DI.pec2Add pblsOrder (punsafeCoerce validRSquared) validCurveA blsC1DI blsC2DI` |

While the CPU budget, memory budget, and script size usage is large for a single operation here, these tests were constructed with identical inputs, so the results in this benchmark group can be directly compared. 

### Negation (Inversion)

The second group of tests concerns negation. Again, we are forced to implement a mixture of typeclass methods (here, `pnegate`) and standalone functions (`pec2Negate`). 

Each of the tests in the group tests a simple negation of the `blsC1`, which is reused without modification. 

All of the tests are directly comparable since the relevant input values are the same. 

The results: 

| Operation | Representation | CPU Cost (% Max Budget)  | Memory Cost (% Max Budget) | Script Size (% Max Budget) | Code 
|---|---|---|---|---|---|
| pnegate | II | 2202412 (0.02%) | 11538 (0.12%) | 556 (3.4%) | `pnegate # blsC1II` |
| pnegate | ID | 1978412 (0.019%) | 10138 (0.1%) | 544 (3.3%) | `pnegate # blsC1ID` | 
| pec2Negate | DD | 2198108 (0.022%) | 10462 (0.1%) | 666 (4%) | `DD.pec2Negate blsC1DD` | 
| pec2Negate | DI | 2486108 (0.024%) | 12262 (0.12%) | 904 (5.5%) | `DI.pec2Negate blsC1DI` | 

### Scaling 

The third group of benchmark tests concerns scaling. Again, we have a split between typeclass methods (`pscalePositive`) and standalone functions (`pec2Scale` with a positive argument). 

These tests clearly demonstrate the severe performance degradation in the `DI` and `DD` cases. We initially attempted to implement tests that scale the `blsC1` point by an integer scalar of `32`. This is indeed how the `II` and `ID` tests are implemented. However, even this relatively small input caused the `DI` and `DD` representations to exceed the CPU budget, so we were forced to reduce the integar scalar by a factor of 8, and the `DI/DD` tests are consequently run with an integer scalar of `4` as the argument. 

The use of different test inputs here means that the test results are not directly comparable. We note that an integer scalar of 32 is, in this context, still relatively small. Consequently, while the different input values preclude a meaningful direct comparison of the results (i.e. in terms of % of the CPU budget consumed), the results (especially the CPU cost) nevertheless clearly demonstrate that the direct representations are not suitable at all, and the indirect representations are only suitable for use on implausibly small scalar values. 

These tests are a subset of all of the simple scaling tests we implemented. We will omit an explication of the further tests because the results are broadly consistent with the results here, and the results presented in this section independently suffice to support our argument. Curious readers can examine the full set of benchmark results located at `goldens/extension-ec.bench.golden`

As a reminder, the `II/ID` and the `DI/DD` benchmarks do not use the same input values due to the previously mentioned performance degradation. As we have described, the Plutarch golden testing machinery used for these benchmarks cannot easily have its budgets 'expanded' for a direct comparison. Thus the actual numbers for the `DI` and `DD` cases would be far higher for identical cases than the results here indicate. 

The results: 

| Operation | Representation | CPU Cost (% Max Budget)  | Memory Cost (% Max Budget) | Script Size (% Max Budget) | Code 
|---|---|---|---|---|---|
|pscalePositive | II | 610629940 (6.1%) | 577789 (5.8%) | 1594 (9.7%) | `pscalePositive blsC1II (punsafeCoerce @_ @PInteger 32)` |
|pscalePositive | ID | 321189456 (3.2%)| 290273 (2.9%) | 1471 (9%) | `pscalePositive blsC1ID (punsafeCoerce @_ @PInteger 32)` | 
|pec2Scale | DD | 1053146819 (10.5%) | 132257 (1.3%) | 2651 (16.2%) | `DD.pec2Scale pblsOrder validRSquared validCurveA blsC1DD 4` | 
|pec2Scale | DI | 1929108917 (19.3%)| 660473 (6.6%) | 2962 (18%) | `DI.pec2Scale pblsOrder (punsafeCoerce validRSquared) validCurveA blsC1DI 4` | 


### Scale-Add 

Our final group of benchmarks concerns a compound operation that scales a point by some scalar and then performs an addition operation with another point. 

This `scale-add` operation is particularly useful for ascertaining the viability of an onchain representation because, as is noted [here](https://static1.squarespace.com/static/5fdbb09f31d71c1227082339/t/5ff394720493bd28278889c6/1609798774687/PairingsForBeginners.pdf) (pg 79), repeated applications of scaling and addition operations are central to the pairing function for verification over the BLS curves. While a full discussion of that pairing function - known as Miller's algorithm - and how we might implement it onchain is outside the scope of this report, it ought to suffice to note that any implementation will involve a large number of scale-then-add operations (exactly how many depends upon the size of the commitments being verified) used with values that are much larger than those in our tests. 

Again, we ran into limitations here that forced us to use an unreasonably small integer scalar lest we exceed the CPU budget. All of the tests consist in adding the `blsC1` point to itself scaled by an integer scalar of `2`. Larger integer scalars cause the benchmarks to fail due to exceeding the CPU budget. 

These results are directly comparable. Unlike the previous benchmark group, we chose the lowest scalar that allows the the `DD/DI` benchmarks here to executive. _Slightly_ higher scalar values may allow the `II/ID` benchmarks to execute without exceeding the limits, but the results nonetheless demonstrate the extremely high cost of our most efficient representation even using trivially small scalar values.  

Here are the results: 

| Operation | Representation | CPU Cost (% Max Budget)  | Memory Cost (% Max Budget) | Script Size (% Max Budget) | Code 
| --- | --- | --- | --- | --- | --- | 
| scale-add | II | 205141864 (2.05%) | 223648 (2.24%) | 3414 (20.8%) | `blsC1II #+ pscaleInteger blsC1II 2` |
| scale-add | ID | 99850088 (1%) | 110316 (1.1%) | 3184 (19.4%) | `blsC1ID #+ pscaleInteger blsC1ID 2` |
| scale-add | DD | 579644274 (5.8%) | 120400 (1.2%) | 5634 (34.4%) | `DD.pec2Add pblsOrder validRSquared validCurveA blsC1DD (DD.pec2Scale pblsOrder validRSquared validCurveA blsC1DD 2)` | 
| scale-add | DI | 1127817205 (11.3%) | 513753 (5.14%) | 5909 (36%) | `DI.pec2Add pblsOrder (punsafeCoerce validRSquared) validCurveA blsC1DI (DI.pec2Scale pblsOrder (punsafeCoerce validRSquared) validCurveA blsC1DI 2)` | 
 
### Benchmark Results Discussion 

The benchmark results reveal a clear pattern: With the exception of the negation/inversion benchmarks, even our most efficient representation still falls considerably short of the CPU and script size requirements to fit on-chain. 

As a reminder, all of the benchmark results presented here are benchmarks of _simple_ computations, each of which may be performed dozens, hundreds, or thousands of times when a pairing function built upon them executes. A pairing function, of course, is one component of a fleshed out ZK proof verification system. While the details will depend somewhat on which scheme is implemented, a cursory look at the [prototype KZG verification function](https://github.com/mlabs-haskell/grumplestiltskin/blob/sean/m4-report/src/Grumplestiltskin/Verify.hs) implemented over BLS that we constructed for Milestone 4 reveals clearly the inadequacy of the representations for the task of verification: 
  1. Prior to computing the pairing, we must perform two scaling operations, which scale by a value (referred to as `r` in our implementation) which, for the cryptographic integrity of verification to be preserved, must be impossible to distinguish from random noise. The overwhelming majority of secure choices for `r` will be *much larger than 32*, since `r` must be a (cryptographically secure) randomly chosen integer. Our most efficient representation (`ID`) is only capable of handling integer scalars of around 1000 or less before exceeding the script budget (this can be easily verified by modifying the test values), and is therefore plainly incapable of working with `r` values necessary for secure verification. This alone conclusively shows that no implementation built off our most efficient representation is viable. 
  2. The script size costs of every basic operation aside from negation are unrealistically high. Our addition tests benchmark simple additions of only two points, and the most efficient representation still uses nearly 15% of the total script budget. Technically speaking, the "script budget" is actually the budget for an entire _transaction_, so is lower than the numbers indicate. But even if we assume we can use the full budget, we must also have space for functions which select and validate inputs, convert between Plutus data encodings and more efficient representations for computational purposes, and so on. A "real" validator that implemented verification would of course require these additional bits of code _and_ other EC point operations, which (again, aside from negation), are also extremely costly in terms of script budget. Therefore, even if we ignore the CPU budget limitations, it is extraordinarily likely that we could not fit a fully realized verifier into the script size budget, and it is not possible to implement verification in a validator. 
  3. Even if we could fit simple examples onchain without exceeding either the CPU or script size budget, we cannot make use of a builtin pairing function like our Milestone 4 prototype does. As hinted at above, we would have to implement the pairing function (Miller's algorithm) using primitives that we have constructed and benchmarked here. There is virtually no chance that we could do this given the existing constraints. But even if we could, somehow, fit an implementation of the pairing function on-chain, we would have to specify that it can only be used with _extremely small commitments_, and could never work with a fully realized ZK proof system involving many commitments (as is commonly produced by ZK circuit machinery). Furthermore, not only must the commitments be small, the coefficients of the polynomials that represent the commitments must also be small, since we have to scale them. Therefore, even if we could fit an implementation of the pairing function onchain without exceeding script size and CPU budgets (and we cannot do this!), it could never lead to a viable ZK verification system. 
  
  
Ultimately, our problems here result from the manner in which we _must_ represent the point at infinity in an affine representation of curve points. In particular, the core of our problem is that we are forced to represent curve points as a _sum type_ in our intermediaries. While this problem is more obvious in the case of direct representations, it is present in a slightly different form for indirect representations as well. 

The benchmarks clearly indicate that a direct representation of `PEC2Intermediate` is always worse than the indirect representation. If we look at the _direct-direct_ `pec2Add`, we can say why this is the case: Every invocation of `pec2Add` requires _many_ pattern matches: One for each `PEC2Intermediate` (to determine if we have the point at infinity), and, in cases where we do not have the point at infinity, additional matches on the `PD2Intermediates` contained in each `PEC2Intermediate` (e.g. via calls to `pd2Square/pd2Divide`, etc). This greatly increases the execution cost of these operations. The situation with respect to script size is no better: These matches are not just computationally expensive, but also expensive in terms of script size. The script size problem is made even worse when we consider the need to explicitly apply all of the auxiliary values in every operation, which leads to comically large script sizes for simple, primitive operations. 

With the _indirect_ representation, because we are working with a CPS encoding, we first have to _evaluate the arguments to determine whether one of them is the point at infinity_. Even if we avoid explicit pattern matching, we cannot get out of having to branch (i.e. here using `pif` instead of `pmatch`) depending on which "arm" of `PEC2Intermediate` we have, because the point at infinity operates as an additive semigroup identity. By the definition of an additive semigroup identity, we must return the other argument if we encounter the point at infinity. Subsequent computations cannot be aware of the results of previous computations that return a `PEC2Intermediate` without evaluating and branching, so we must _always_ evaluate the arguments and then branch. By this point it should not be surprising that this procedure entails significant costs, both in terms of CPU budget and script size, as reflected in the benchmarks. 

An astute Haskeller might recognize that over-evaluation in this context would not be a problem in Haskell itself, because Haskell has true call-by-need evaluation, and therefore results of prior computation can be _shared_, which would greatly reduce the number of superfluous evaluations here and lead to significantly better performance. UPLC, however, is a strict language, and is subject to the same shortfalls as any other strict language that lacks the resources to implement efficient laziness and sharing. We note that this problem - over-evaluation of previously computed results - is not a problem specific to UPLC but crops up more generally in strict languages without an "escape hatch" for call-by-need evaluation or the means to emulate it. Because the UPLC `delay` primitive does not implement real call-by-need evaluation (with sharing), UPLC simply does not provide the tools needed to implement an efficient indirect representation. 

Ultimately, the performance issues with both direct and indirect representations are due to the fact that _any_ affine representation of `PEC2Intermediate` (or anything analogous to it) must (at least morally) be a sum type, where one arm must be the point at infinity. The Boehm-Berarducci (CPS) encoding used in the indirect representations may not look like a sum type, but we must still evaluate and branch on the presence or absence of the point at infinity, so no matter what we do, we are stuck with poor performance. The indirect representation saves us from some excessive algorithmic costs (i.e. those incurred by repeated, explicit pattern matches), but we occur massive incidental costs due to the (inescapable) need to repeatedly evaluate. Future modifications to UPLC may make the indirect representation viable, but as things are now, it does not present enough of an improvement over the direction representation to support on-chain verifiction within the current protocol parameters (or any foreseeable future parameters, given the extreme script size and CPU costs demonstrated in our benchmarks). 

## Alternatives Considered (and Rejected)

The affine (Euclidean) representation is not the only representation of EC points we might use. In addition to the affine representation, one could implement a naive projective representation or some development thereof (e.g. Jacobian, Chudnovsky-Jacobian, or Modified Jacobian) of EC points and field extensions. 

The fundamental difference between the affine representation and the projective alternatives is that the projective alternatives represent points in 3d space, and are, therefore, capable of representing the point at infinity using proper coordinates, without the need of a sum type or special constructor.

Adopting a projective representation in some form would then appear to solve our problem. Unfortunately, this appearance is deceiving. 

While a projective representation would save us from the incidental costs (e.g. excessive pattern matching or over-evaluation) that we cannot otherwise escape from, we would be forced incur significant _algorithmic_ costs due to the inherent inefficiency of group operations defined over a projective representation. Even in the projective representation, addition and multiplication of elements in a field extension require multiplication and squaring in the underlying field. As we noted in the Milestone 2 report, all non-affine representations have a significantly higher algorithmic cost than their affine equivalents: 

| Operation | Affine cost | Projective cost | Jacobian cost | Chudnovsky-Jacobian cost | Modified Jacobian cost |
|---|---|---|---|---|---|
| Addition of points | 5 | 14 | 16 | 14 | 18 |
| Doubling of point | 5 | 12 | 10 | 11 | 8 |

We note that these operations in the underlying field (which are not improved by choosing a different representation of field extension elements) are themselves intrinsically costly, as our benchmarks in `ec.bench.golden` show (table is an excerpt of those results): 

| Operation | CPU Cost | Memory Cost | Size | 
| --- | --- | --- | --- | 
| pecAdd | 4997325 | 10861 | 710 | 
| pecScale | 22121638 | 53721 | 759 | 
| pecInvert | 359408 | 1707 | 116 | 
| pecDouble | 4816986 | 10794 | 230 | 

A quick glance at the benchmark results for operations in the underlying field makes it very clear that a non-affine representation of field extensions, even if it leads to a marginal improvement over our affine representation, cannot deliver the exponential performance improvements necessary to make on-chain verification viable. This should not be surprising, since the primary benefit of non-affine representations is that they are able to avoid negations (inversions), which are typically computationally expensive. This gives us no practical benefit here, since negations (inversions) are _cheap_ relative to the other operations, and therefore we would not see any substantial improvements by switching to a non-affine representation.

While we are hopeful that future improvements to UPLC will allow us to achieve the goal we set for ourselves with this milestone, we believe that the data presented and our analysis of it conclusively demonstrates that we cannot achieve our goal here - and that no one else could do sufficiently better. We are fundamentally caught between the high incidental costs of the affine representation and the high algorithmic costs of all non-affine representations.
