# ZK Verifier Prototype 

## Introduction 
We attempted to implement a BLS12-381 KZG proof verifier prototype using primitives which are parameterized by fields and curves, in the Plutarch eDSL for UPLC script generation, as required by Milestone 3. In order to implement a ZK proof verifier, we first had to design and implement representations of, and operations on, finite field extensions, which can be found in the `src/Grumplestiltskin/Degree1` and `src/Grumplestiltskin/Degree2` directories. (These primitives can support other curves, but BLS was the target for our prototype.)

Unfortunately, we ran into intractable problems during this step that made it clear to us that a BLS verifier built on top of these primitives is not viable. The limitations we discovered in M2 proved even more limiting in the case of operations over second degree field extensions, such that even simple test cases (i.e. of the primitive operations, not of verification) approached or exceeded limits set but Cardano protocol parameters. The current state of UPLC, therefore, forces us into a dilemma: Representations of field extensions which lead to acceptable script sizes incur extreme CPU and memory costs, whereas representations that lead to acceptable CPU and memory costs produce script sizes which reach or exceed the limits even in artificially small and simple test cases.

We believe that our results demonstrate that no implementation could satisfy the performance requirements necessary for on-chain use, and that our failure here is the result of a true dilemma.

Our aim in this report is to explain why field extensions are necessary for parametric proof verification, explain the the multiple ways we represented field extensions, provide evidence that none of our representations are feasible for onchain verification given current or foreseeable protocol parameters, and finally, to make the case that any projective representation - the only alternative to our affine approach here - can do no better (and will almost certainly do much worse).

## Goals and Priorities 

Our primary goal for the milestone was to implement a BLS KZG verifier prototype using parametric primitives. Because the G2 curve is a second degree extension of the G1 curve, and because a pairing function over these curves is an essential component of any verifier. To that end, our initial goal and first priority was to implement parametric primitives for second degree field extensions. 

As indicated in the introduction, we ran into intractable performance problems when attempting to implement these primitives. While it would have been conceptually possible to build an extremely inefficient verifier on top of our primitives, doing so would have no purpose because our preliminary results clearly demonstrate a severe performance blowout in the primitive operations on small and simple test cases. 

In the following sections, we will explain the various ways in which we attempted to represent second-degree field extensions and primitive operations over them, and then provide evidence which we believe demonstrates (with a high degree of certainty) that neither our implementation nor any other can yield a viable onchain implementation of second degree field extensions and operations over them. 

## Implementation of Second Degree Field Extensions 

### Types

In our Milestone 2 work, we implemented datatypes and group operations over elliptic curves using two distinct representations: A direct (i.e. SOP-encoded) representation, and an indirect (i.e. Boehm-Berarducci form) representation. Group operations in M2 were defined over a type (`PECIntermediatePoint`) that represents an intermediate computation on points. (See the M2 report for details.) 

In our milestone 3 work, we continued along this path when designing representations and operations over field extensions. However, since we are now dealing with elements of field extensions _and_ curve points, we must implement two different kinds of intermediate computations: 

  - `PD2Intermediate`, which represents a computation that, when run, produces an _element of a second degree field extension_
  - `PEC2Intermediate`, which represents a computation that, when run, produces _a point on some elliptic curve_
  
Each of these types can, in a manner following M2, be represented in a direct (SOP) or indirect (CPS/BB form) way. The indirect and direct representations of `PD2Intermediate` can be found, respectively, in the `Grumplestiltskin.Degree2.Galois` and `Grumplestiltskin.Degree2.GaloisDirect` modules.  

Because `PEC2Intermediate` can itself be represented directly or indirectly, and because it must refer to `PD2Intermediate` results (which may be represented directly or indirectly), there are four possible variants of `PEC2Intermediate`: 
  1. Direct `PEC2Intermediate` using direct `PD2Intermediate`
  2. Direct `PEC2Intermediate` using indirect `PD2Intermediate`
  3. Indirect `PEC2Intermediate` using direct `PD2Intermediate`
  4. Indirect `PEC2Intermediate` using indirect `PD2Intermediate`
  
These can be found, respectively, in the `EllipticCurveDD, EllipticCurveDI, EllipticCurveID, EllipticCurveII` modules in the `src/Grumplestiltskin/Degree2` directory. 

The "result types" of the intermediate computations, `PD2Element` and `PEC2Point` (which is comprised of `PD2Element`s) have only one representation (the direct one), and can be found in `Degree2.Element` and `Degree2.AffinePoint` respectively, along with their Haskell-level counterparts. 

## Benchmarks 

We implemented a benchmark suite to compare the performance tradeoffs between various ways we represented field extensions and their operations. Each benchmark test here implements a simple group operation using the designated representation (e.g. `DI` means a direct `PEC2Intermediate` with an indirect `PD2Intermediate`, and so on). 

The implementation of the benchmarks can be found in `test/extension-ec/Main.hs`, and the cached golden results can be found in `goldens/extension-ec.bench.golden`. There are other benchmarks and tests in our test directory, but only these are particularly pertinent for this report. Wherever possible, we use pre-evaluated terms to minimize the amount of onchain computation. 

Here are the benchmarks from `extension-ec.bench.golden`: 

```
pec2OnCurve {"exBudgetCPU":11382843,"exBudgetMemory":40068,"scriptSizeBytes":2005}
#+ (II) {"exBudgetCPU":100291545,"exBudgetMemory":104792,"scriptSizeBytes":2547}
#+ (ID) {"exBudgetCPU":48214005,"exBudgetMemory":48183,"scriptSizeBytes":2440}
pec2Add (DD) {"exBudgetCPU":49275939,"exBudgetMemory":51431,"scriptSizeBytes":3332}
pec2Add (DI) {"exBudgetCPU":101049479,"exBudgetMemory":106140,"scriptSizeBytes":3093}
pnegate (II) {"exBudgetCPU":2202412,"exBudgetMemory":11538,"scriptSizeBytes":556}
pnegate (ID) {"exBudgetCPU":1978412,"exBudgetMemory":10138,"scriptSizeBytes":544}
pec2Negate (DD) {"exBudgetCPU":2198108,"exBudgetMemory":10462,"scriptSizeBytes":666}
pec2Negate (DI) {"exBudgetCPU":2486108,"exBudgetMemory":12262,"scriptSizeBytes":904}
pscalePositive (II) {"exBudgetCPU":610629940,"exBudgetMemory":577789,"scriptSizeBytes":1594}
pscalePositive (ID) {"exBudgetCPU":321189456,"exBudgetMemory":290273,"scriptSizeBytes":1471}
pscaleNatural (II) {"exBudgetCPU":610778273,"exBudgetMemory":578390,"scriptSizeBytes":1607}
pscaleNatural (ID) {"exBudgetCPU":321337789,"exBudgetMemory":290874,"scriptSizeBytes":1483}
pscaleInteger positive (II) {"exBudgetCPU":610966110,"exBudgetMemory":579291,"scriptSizeBytes":1925}
pscaleInteger positive (ID) {"exBudgetCPU":321525626,"exBudgetMemory":291775,"scriptSizeBytes":1789}
pec2Scale positive (DD, 8 times smaller) {"exBudgetCPU":1053146819,"exBudgetMemory":132257,"scriptSizeBytes":2651}
pec2Scale positive (DI, 8 times smaller) {"exBudgetCPU":1929108917,"exBudgetMemory":660473,"scriptSizeBytes":2962}
pscaleInteger negative (II) {"exBudgetCPU":613326420,"exBudgetMemory":589145,"scriptSizeBytes":1927}
pscaleInteger negative (ID) {"exBudgetCPU":321525626,"exBudgetMemory":291775,"scriptSizeBytes":1789}
pec2Scale negative (DD, 8 times smaller) {"exBudgetCPU":1055626007,"exBudgetMemory":140626,"scriptSizeBytes":2661}
pec2Scale negative (DI, 8 times smaller) {"exBudgetCPU":1931620105,"exBudgetMemory":669042,"scriptSizeBytes":2972}
scale-add (II) {"exBudgetCPU":205141864,"exBudgetMemory":223648,"scriptSizeBytes":3414}
scale-add (ID) {"exBudgetCPU":99850088,"exBudgetMemory":110316,"scriptSizeBytes":3184}
scale-add (DD) {"exBudgetCPU":579644274,"exBudgetMemory":120400,"scriptSizeBytes":5634}
scale-add (DI) {"exBudgetCPU":1127817205,"exBudgetMemory":513753,"scriptSizeBytes":5909}
```

Before discussing _why_ performance is (intractably) so poor, we must explain just _how_ devastating these benchmark results are for the prospect of viable on-chain verification using parametric primitives. 

The [current protocol parameters](https://book.world.dev.cardano.org/environments/mainnet/alonzo-genesis.json) give the following values for memory and CPU limits: 

```
exUnitsMem: 10000000
exUnitsSteps: 10000000000
```

The `scale-add` benchmarks are a particularly useful example of a simple operation which, in any implementation of a KZG verification procedure, will must repeated a great number of times. The number of calls to that operation will vary in proportion to the size of the commitment being verified, but it is reasonable to expect that even a small circuit used in PLONK style verification will require at least hundreds - and quite likely thousands - of scale-add procedures. See page 79 of [this resource](https://static1.squarespace.com/static/5fdbb09f31d71c1227082339/t/5ff394720493bd28278889c6/1609798774687/PairingsForBeginners.pdf) for a detailed exposition of Miller's algorithm (the pairing function for BLS-381) - though all that matters for our purposes is that Miller's algorithm is the most efficient BLS pairing function and that it requires a large number of these operations. As the resource notes: "Miller’s algorithm is essentially the straightforward double-and-add algorithm for elliptic curve point multiplication [...]" (78), so this double-and-add operation must be very efficient for a viable onchain verifier. 

The benchmarks conclusively demonstrate that this operation is nowhere near efficient enough. Each variant of `scale-add` uses a nontrivial amount of the maximum script CPU budget (values are percentage of the maximum budget for each variant above): 

```
II: ~2%
ID: ~1%
DD: ~6%
DI: ~11%
```

Even the most efficient variant is nowhere near efficient enough for use in a context where it may be called hundreds or thousands of times. Furthermore, the testing context here is highly idealized, in that we are ignoring the (necessary) overhead which results from locating datum or redeemer inputs, deserializing those inputs (etc). 

A blowout in script CPU budget, however, is not the only problem - and perhaps not even the most severe problem. The [current Shelley genesis file for Cardano mainnet](https://book.world.dev.cardano.org/environments/mainnet/shelley-genesis.json) gives a script size limit of `16384` bytes. Again, if we render the benchmark values for `scale-add` as percentages, this time referenced against the maximum script size, we get: 

```
II: ~21%
ID: ~19%
DD: ~34%
DI: ~36%
```

Again, it is plain that these operations are not suitable for a context where they may need to be used hundreds or thousands of times. Even these simple test cases use between (roughly) 1/5 and 1/3 of the transaction size budget. The only sensible conclusion is that a viable on-chain implementation of a fully-realized verifier would require an exponential reduction in *both* script size *and* execution units.  

This suffices to demonstrate that none of the variants implemented here are adequate for onchain usage. However, in order to support our claim that no other variant can do better, we must first explain why we chose the representations we did and explicate the ultimate source of this performance blowout. 

## Discussion I: The Affine Representation (& Why It Fails)

Every combination of direct/indirect representations we used to implement curve points, field extensions, and group operations over them is an affine (or Euclidean) representation. Put simply, this means that points are represented in the way you would naively expect, that is, as coordinates on a 2d plane. 

Our direct representations are, again, straightforward. For example, the *direct* `PD2Intermediate` type is morally equivalent to a tuple of integers, and the *direct-direct* `PEC2Intermediate` type a pair of those "tuples" plus a constructor to represent the point at infinity: 

```
-- GaloisDirect.hs
data PD2Intermediate (s :: S) = PD2Intermediate (Term s PInteger) (Term s PInteger)

-- EllipticCurveDD.hs

data PEC2Intermediate (s :: S)
    = PEC2InfinityI
    | PEC2PointI (Term s PD2Intermediate) (Term s PD2Intermediate)
```

In order to perform operations over EC points (and elements of field extensions), we require some auxiliary values - in particular, the _irreducible_ and the _field order_, which are effectively constants that vary _per curve_, but which must be supplied as arguments in the direct representation, otherwise our operations would not be parametric over arbitrary curves and extensions. For instance, `pec2Add` for the `DD` representation looks like: 

```
pec2Add ::
    forall (s :: S).
    Term s PPositive ->
    Term s PPositive ->
    Term s PD2Element ->
    Term s PEC2Intermediate ->
    Term s PEC2Intermediate ->
    Term s PEC2Intermediate
pec2Add fieldMod rSquared curveA t1 t2 = pmatch t1 $ \case
    PEC2InfinityI -> t2
    PEC2PointI x1 y1 -> pmatch t2 $ \case
        PEC2InfinityI -> t1
        PEC2PointI x2 y2 -> plet (pd2ToElem fieldMod x1) $ \x1' ->
            plet (pd2ToElem fieldMod x2) $ \x2' ->
                plet (y1 #- y2) $ \yDiff ->
                    pif
                        (x1' #== x2')
                        ( pif
                            (pd2ToElem fieldMod yDiff #== pd2Zero)
                            -- Double
                            (pec2Double' # fieldMod # rSquared # curveA # x1 # y1)
                            -- Infinity
                            (pcon PEC2InfinityI)
                        )
                        -- Add normally
                        ( plet (pd2Divide fieldMod rSquared yDiff (x1 #- x2)) $ \lambda ->
                            plet ((pd2Square rSquared lambda #- x1) #- x2) $ \newX ->
                                pcon . PEC2PointI newX $ pd2Times rSquared lambda (x1 #- newX) #- y1
                        )
```

Where the first two arguments are these auxiliary values. The benchmarks clearly indicate that a direct representation of `PEC2Intermediate` is always worse than the indirect representation. If we look at the _direct-direct_ `pec2Add`, we can say why this is the case: Every invocation of `pec2Add` requires _many_ pattern matches: One for each `PEC2Intermediate` (to determine if we have the point at infinity), and, in cases where we do not have the point at infinity, additional matches on the `PD2Intermediates` contained in each `PEC2Intermediate` (e.g. via calls to `pd2Square/pd2Divide`, etc). This greatly increases the execution cost of these operations. The situation with respect to script size is no better: These matches are not just computationally expensive, but also expensive in terms of script size. The size blowout is made even worse when we consider the need to explicitly apply all of the auxiliary values in every operation, which leads to comically large script sizes for simple, primitive operations. 

The situation is slightly better - though still far from viable - with the indirect representation. Unlike the direct representation, the indirect representation seems to factor out applications of the auxiliary values using a Boehm-Berarducci encoding (a CPS encoding, if you like): 

```
-- Galois.hs 
newtype PD2Intermediate (s :: S)
    = PD2Intermediate
        (forall (r :: S -> Type). Term s (PNatural :--> PPositive :--> (PInteger :--> PInteger :--> r) :--> r))

-- EllipticCurveII.hs
newtype PEC2Intermediate (s :: S)
    = PEC2Intermediate
        ( forall (r :: S -> Type).
          Term
            s
            ( PPositive
                :--> PPositive
                :--> PD2Element
                :--> PDelayed r
                :--> (PD2Element :--> PD2Element :--> r)
                :--> r
            )
        )
```

While we do gain the benefits that accrue from only having to supply the auxiliary values once, i.e. during final evaluation of a `PEC2Intermediate` to get a result, we run into another problem, also related to the point at infinity. Here, we implement the addition operation using the `PAdditiveSemigroup` type class, with the instance (again from `EllipticCurveII.hs`): 

```
instance PAdditiveSemigroup PEC2Intermediate where
    t1 #+ t2 = pmatch t1 $ \(PEC2Intermediate k1) ->
        pmatch t2 $ \(PEC2Intermediate k2) ->
            pcon $ PEC2Intermediate $ plam $ \fieldMod rSquared curveA whenInf whenNot ->
                k1
                    # fieldMod
                    # rSquared
                    # curveA
                    # pdelay (k2 # fieldMod # rSquared # curveA # whenInf # whenNot)
                    # plam
                        ( \x1 y1 ->
                            k2
                                # fieldMod
                                # rSquared
                                # curveA
                                # pdelay (k1 # fieldMod # rSquared # curveA # whenInf # whenNot)
                                # plam
                                    ( \x2 y2 ->
                                        plet (pd2FromElem x1) $ \x1' ->
                                            plet (pd2FromElem x2) $ \x2' ->
                                                plet (pd2FromElem y1) $ \y1' ->
                                                    plet (pd2FromElem y2) $ \y2' ->
                                                        let rSquared' = punsafeCoerce rSquared
                                                         in plet (y1' #- y2') $ \yDiff' ->
                                                                pif
                                                                    (x1 #== x2)
                                                                    ( pif
                                                                        (pd2ToElem rSquared' fieldMod yDiff' #== pd2Zero)
                                                                        -- Double
                                                                        (pec2Double' # fieldMod # rSquared # curveA # whenInf # whenNot # x1' # y1' # y1)
                                                                        -- Infinity
                                                                        (pforce whenInf)
                                                                    )
                                                                    -- Add
                                                                    ( plet (pd2Divide yDiff' (x1' #- x2')) $ \lambda ->
                                                                        plet ((pd2Square lambda #- x1') #- x2') $ \newX ->
                                                                            plet ((lambda #* (x1' #- newX)) #- y1') $ \newY ->
                                                                                whenNot # pd2ToElem rSquared' fieldMod newX # pd2ToElem rSquared' fieldMod newY
                                                                    )
                                    )
                        )
    pscalePositive t p = go # t # pupcast p
      where
        go :: forall (s :: S). Term s (PEC2Intermediate :--> PInteger :--> PEC2Intermediate)
        go = phoistAcyclic $ pfix $ \self -> plam $ \t' p' -> pmatch t' $ \(PEC2Intermediate k1) ->
            pcon $ PEC2Intermediate $ plam $ \fieldMod rSquared curveA whenInf whenNot ->
                k1
                    # fieldMod
                    # rSquared
                    # curveA
                    # whenInf
                    # plam
                        ( \x y ->
                            pif
                                (p' #== 1)
                                (whenNot # x # y)
                                ( plet (pec2Double (self # t' #$ pquot # p' # 2)) $ \doubled ->
                                    punsafeCase
                                        (prem # p' # 2)
                                        [ popaque $ pmatch doubled $ \(PEC2Intermediate k2) ->
                                            k2 # fieldMod # rSquared # curveA # whenInf # whenNot
                                        , popaque $ pmatch (doubled #+ t') $ \(PEC2Intermediate k2) ->
                                            k2 # fieldMod # rSquared # curveA # whenInf # whenNot
                                        ]
                                )
                        )
```

At a glance, it should be obvious even to readers without significant Plutarch experience that this is horrendously ugly and nigh-unreadable code, which is itself a problem (albeit a comparatively minor one). The main issue, however, is that with the _indirect_ representation, because we are working with a CPS encoding, we first have to _evaluate the arguments to determine whether one of them is the point at infinity_. Even if we avoid explicit pattern matching, we cannot get out of having to branch (i.e. here using `pif` instead of `pmatch`) depending on which "arm" of `PEC2Intermediate` we have, because the point at infinity operates as an additive semigroup identity. By the definition of an additive semigroup identity, we must return the other argument if we encounter the point at infinity. Subsequent computations cannot be aware of the results of previous computations that return a `PEC2Intermediate` without evaluating and branching, so we must _always_ evaluate the arguments and then branch. By this point it should not be surprising that this procedure entails significant costs, both in terms of CPU budget and script size, as reflected in the benchmarks. 

An astute Haskeller might recognize that over-evaluation in this context would not be a problem in Haskell itself, because Haskell has true laziness, and therefore results of prior computation can be _shared_, which would greatly reduce the number of superfluous evaluations here and lead to significantly better performance. UPLC, however, is a strict language, and is subject to the same shortfalls as any other strict language that lacks the resources to implement efficient laziness and sharing. We note that this problem - over-evaluation of previously computed results - is essentially the same problem that crops up in "naive" PureScript which does not make use of the laziness library, and can similarly lead to extreme performance degradation in that language. Because the UPLC `delay` primitive does not implement real laziness (with sharing), UPLC simply does not provide the tools needed to implement an efficient indirect representation. 

Ultimately, the performance issues with both direct and indirect representations are due to the fact that _any_ affine representation of `PEC2Intermediate` (or anything analogous to it) must (at least morally) be a sum type, where one arm must be the point at infinity. The Boehm-Berarducci (CPS) encoding used in the indirect representations may not look like a sum type, but we must still evaluate and branch on the presence or absence of the point at infinity, so no matter what we do, we are stuck with poor performance. The indirect representation saves us from some excessive algorithmic costs (i.e. those incurred by repeated, explicit pattern matches), but we occur massive incidental costs due to the (inescapable) need to repeatedly evaluate. Future modifications to UPLC may make the indirect representation viable, but as things are now, it does not present enough of an improvement over the direction representation to support on-chain verifiction within the current protocol parameters (or any foreseeable future parameters, given the extreme script size and CPU costs demonstrated in our benchmarks). 

## Discussion II: Can't Do Better 

The affine (Euclidean) representation is not the only representation of EC points we might use. In addition to the affine representation, one could implement a naive projective representation or some development thereof (e.g. Jacobian, Chudnovsky-Jacobian, or Modified Jacobian) of EC points and field extensions. 

The fundamental difference between the affine representation and the projective alternatives is that the projective alternatives represent points in 3d space, and are, therefore, capable of representing the point at infinity using proper coordinates, without the need of a sum type or special constructor.

Adopting a projective representation in some form would then appear to solve our problem. Unfortunately, this appearance is deceiving. 

While a projective representation would save us from the incidental costs (e.g. excessive pattern matching or over-evaluation) that we cannot otherwise escape from, we would be forced incur significant _algorithmic_ costs due to the inherent inefficiency of group operations defined over a projective representation. Even in the projective representation, addition and multiplication of elements in a field extension require multiplication and squaring in the underlying field. As we noted in the Milestone 2 report, all non-affine representations have a significantly higher algorithmic cost than their affine equivalents: 

| Operation | Affine cost | Projective cost | Jacobian cost | Chudnovsky-Jacobian cost | Modified Jacobian cost |
|---|---|---|---|---|---|
| Addition of points | 5 | 14 | 16 | 14 | 18 |
| Doubling of point | 5 | 12 | 10 | 11 | 8 |

We note that these operations in the underlying field (which are not improved by choosing a different representation of field extension elements) are themselves intrinsically costly, as our benchmarks in `ec.bench.golden` show: 

```
pecAdd {"exBudgetCPU":4997325,"exBudgetMemory":10861,"scriptSizeBytes":710}
pecScale {"exBudgetCPU":22121638,"exBudgetMemory":53721,"scriptSizeBytes":759}
pecScale negative {"exBudgetCPU":23333778,"exBudgetMemory":58136,"scriptSizeBytes":767}
pecInvert {"exBudgetCPU":359408,"exBudgetMemory":1707,"scriptSizeBytes":116}
pecDouble {"exBudgetCPU":4816986,"exBudgetMemory":10794,"scriptSizeBytes":230}
pecToPoint {"exBudgetCPU":715630,"exBudgetMemory":2704,"scriptSizeBytes":143}
pecFromPoint {"exBudgetCPU":144100,"exBudgetMemory":1000,"scriptSizeBytes":55}
ptryFrom {"exBudgetCPU":5066257,"exBudgetMemory":22397,"scriptSizeBytes":527}
pecOnCurve {"exBudgetCPU":1714413,"exBudgetMemory":5036,"scriptSizeBytes":112}
```

A quick glance at the benchmark results for operations in the underlying field makes it very clear that a non-affine representation of field extensions, even if it leads to a marginal improvement over our affine representation, cannot deliver the exponential performance improvements necessary to make on-chain verification viable. 

While we are hopeful that future improvements to UPLC will allow us to achieve the goal we set for ourselves with this milestone, we believe that the data presented and our analysis of it conclusively demonstrates that we cannot achieve our goal here - and that no one else could do sufficiently better. We are fundamentally caught between the high incidental costs of the affine representation and the high algorithmic costs of all non-affine representations.
