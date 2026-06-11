# Milestone 5 Report

## Introduction 

As the conclusions presented in the [Milestone 3 report][M3] demonstrate, the current limitations of UPLC are such that implementing a parametric onchain zero-knowledge proof verifier is not viable. Performance problems that emerged when attempting to implement operations on higher-order field extensions and curves over those extensions were so severe as to render our initial goal intractable under current protocol parameters. Due to these limitations, we were forced to halt our attempt to develop this verification framework. These limitations, however, originate from contingent (rather than essential) features of UPLC, and the language could be modified in such a way as to make our original goal viable. 

In this report, we will outline three proposed changes to UPLC: Call by need evaluation, mutability, and a better implementation of arrays. Although mutability in UPLC would almost certainly solve many of our performance problems, we believe that its consequences, both for UPLC itself and for the Cardano ecosystem as a whole, are too severe to recommend. Call-by-need evaluation is a less disruptive change, but may not yield significant enough improvements to make our original goal viable. We propose better array support as a middle ground that is likely to solve our performance problems without significant consequences for the ecosystem. 

In this report, we will give a brief account of each of our proposed modifications to UPLC and explain how we believe they will solve the problems we encountered. We will also discuss the tradeoffs of each proposed change, with particular attention to the amount of disruption to the existing UPLC codebase and Cardano more broadly (where relevant). 

## Call-by-Need (Laziness)

In the [Milestone 3 report][M3], we identified excessive evaluation of previously computed results as a primary cause of the performance degradation we encountered, particularly with respect to the indirect representations. In the context of a functional language, one straightforward solution to the problems we encountered is adding support for call-by-need (also commonly known as "lazy") evaluation. Call-by-need evaluation is well-studied, most notably in Haskell itself, where it is the default evaluation strategy. 

As we explained in the [Milestone 3 report][M3], the most efficient implementation of operations on curve points over finite field extensions was an indirect representation[^2] which makes use of Boehm-Berarducci forms. However, using this representation, we encountered a severe performance degradation caused by over-evaluation of previously computed terms in point addition, which has a significant impact on the performance of fundamental scaling operations (since the latter consist in potentially many additions). The ultimate source of this performance degradation, as we explained, is the need to constantly determine whether some previous result is or is not the point at infinity.

At a glance, one might think that UPLC supports call-by-need evaluation with the `delay` and `force` primitives. Although `force` and `delay` do allow for deferred evaluation, the way in which they are currently implemented in UPLC does not provide the most important (for our purposes) benefit of call-by-need evaluation as it is implemented in a language like Haskell: Memoization or caching of previously computed results, more colloquially known as *sharing*. While some sources define call-by-need evaluation simply in terms of deferral, nearly every language that supports call-by-need evaluation also supports sharing. Because deferred evaluation without memoization greatly diminishes the practical benefits of laziness, when we refer to call-by-need evaluation here, we mean: 

> In lazy [call-by-need] languages, arguments are evaluated in a demand-driven fashion; they are initially passed in unevaluated form and are evaluated only when (and if!) the computation needs the results to continue. Furthermore, once a given argument is evaluated, the value of that argument is cached so that, if it is ever needed again, it can be looked up rather than recomputed.[^1]

This is the sort of call-by-need evaluation implemented in GHC Haskell. UPLC uses call-by-value ("strict") evaluation by default, but this is not a problem on its own. Other functional languages (e.g. PureScript) use a call-by-value evaluation strategy, but provide mechanisms for implementing or emulating call-by-need constructs. UPLC, unfortunately, lacks the mechanisms to support call-by-need with memoization or caching in any real form. Through `force` and `delay`, UPLC does support demand-driven consumption of arguments. However, because `delay`, as it is currently implemented, _only_ defers a computation, and because `force` _only_ evaluated a delayed computation (i.e. without caching the result), UPLC only supports partial call-by-need evaluation. The difference between partial and full support can be better understood with a contrasting Haskell example. Consider the Haskell expression: 

```haskell
-- idiomatically:
let x = 10 ^ 10 
in x + x 

-- equivalently, by desugaring the `let`: 
(\x -> x + x) (10^10)
```

In Haskell, the expression `10^10` is only computed _once_ and is cached after evaluation. We can attempt to mimic this in UPLC (which is presented here with Haskell-like pseudocode due to the lack of a standard "readable" UPLC representation): 

```haskell
(\x -> force x + force x) (delay (10^10))
```

Doing so will defer the evaluation of `10^10` until it is forced, but because no caching or memoization occurs, the expression `10^10` must be evaluated _twice_ here. While this simple example illustrates the basic problem, in practice we end up being forced to over-evaluate previously computed results _many_ times - not just twice. This leads to significant indicental costs which give rise to many of the performance problems we encountered in our benchmarks. 

Call-by-need evaluation with sharing would immediately solve this problem. Because the results of previous computations would be cached, excessive evaluations of previously computed results would disappear, which we anticipate would provide a substantial performance boost to our most efficient representation. 

Call-by-need evaluation would also be minimally disruptive to UPLC at it exists now. While there are several ways that it could be implemented, the most straightforward would be to simply modify the behavior of the existing `force` and `delay` builtins to perform caching or memoization. This may require nontrivial modifications to the UPLC evaluation machinery, but should not affect UPLC's public API at all. Call-by-need evaluation is well-understood, with a solid theoretical basis, has been implemented in other functional languages, and [initial exploratory work][UPLC-Laziness] on modifying `force` and `delay` in UPLC has shown the approach to be viable.

However, there are some drawbacks to call-by-need as a solution to our problems. While we are certain that call-by-need evaluation will _improve_ the performance of our best implementation, we are less certain that the improvement will be _significant enough_ to make onchain verification viable given protocol limits. Strictly speaking, it is impossible to know this, because this change may well necessitate adjusting the costing parameters for `force` and `delay`, as these builtins would now do more work at a hardware level than they do at present. Determining the new costing parameters is, on its own, a nontrivial problem, and likely depends on the details of the changes to UPLC evaluation machinery. 

Furthermore, even on the assumption that call-by-need does lead to a viable onchain verifier, it still necessitates the use of a Boehm-Berarducci representation of curve points for curves over higher order finite field extensions which is unintuitive and awkward to work with. Boehm-Berarducci forms force us to use a continuation passing style in functions, which generates a significant amount of syntactic noise. A simple example demonstrates the awkardness (from `src/Grumplestiltskin/Degree2/EllipticCurveID.hs`): 

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

While this is not a decisive consideration, it is worth noting if only because both mutability and better arrays would facilitate writing code (and designing datatypes) in a much more straightforward and readable way, and would therefore likely have more significant practical benefits for Plutus development in general. 

## Mutability 

The second option for modifying UPLC so that it can facilitate performant onchain verification is to add _mutability_ to the language. Mutability would, effectively, allow us to achieve the benefits of call-by-need evaluation by performing our own caching and memoization. Whereas in call-by-need, the evaluation machinery would handle storing previously computed results so that they do not need to be re-evaluated when passed to subsequent computations, UPLC with mutability would allow us to store the results directly in a mutable variable that could be passed to subsequent computations.  

For our purposes, "local" mutability would suffice. By this we mean mutability that is essentially analogous to Haskell's `ST`, where variables must be explicitly tagged as mutable and cannot escape their computational context. It is likely that an unsafe parametric datatype representing a mutable reference, such as: 

```haskell
newtype MutRef a = MutRef (IORef a)
```

Could be grafted onto `DefaultUni` fairly easily and without the need for significant alternations to the UPLC type system. However, we believe that doing so would not merely be unwise, but unacceptably reckless. Grafting this type (or some equivalent that uses another flavor of mutable reference) onto `DefaultUni` would introduce, effectively, global mutable variables to UPLC. The issues that stem from global mutable variables are well-known: Global mutable state makes programs much harder to reason about, much harder to debug, and much less safe. Given that the purpose of UPLC is to facilitate smart contracts, which ought to be as easy to reason about and debug, and ought to be as safe as possible to reduce the chance of a vulnerability that may have dire financial consequences, introducing global mutable state to UPLC seems contrary to the purpose UPLC was designed for. 

Mutability is incredibly powerful, and can easily be used to obtain all of the benefits of call-by-need evaluation: Instead of relying upon the evaluator's implementation of call-by-need to cache or memoize previously computed results, we can store the results of previous computations directly in mutable variables, which achieves the same effect. 

This [implementation][SOLIDITY] of elliptic curve point scaling in solidity (which is currently deployed in live Ethereum contracts) demonstrates the manner in which mutability can be used to implement EC operations succinctly and without any exotic representations: 

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

It is important to note here that this solidity implementation of point scaling uses the Jacobian representation of EC points, which is a projective representation, whereas our implementation uses the affine representation. The primary relevant difference is that the Jacobian representation allows for a direct representation of the point at infinity (using the `z` coordinate), whereas with the affine representation we must make use of a sum type (again, see the [Milestone 3 report][M3] for more discussion). 

However, this difference in representation is not particularly significant in our context. Again, the main source of the performance degradation in our implementation is that we need to repeatedly re-evaluate already computed arguments to check whether we have the point at infinity during addition. In this solidity implementation, there is no excessive evaluation because the intermediary results are cached in the `qx, qy, qz` variables until they need to be used for a subsequent computation (or returned, if there are no subsequent computations).

In our case, the benefits from mutability would be significant. As with call-by-need evaluation, mutability allows us to avoid re-computing previously computed results. But unlike call-by-need evaluation, mutability would allow for writing code in a straightforward style without resorting to Boehm-Berarducci forms to represent datatypes or (consequently) being forced to write functions in a convoluted and awkward continuation passing style. Moreover, mutability is such a powerful tool that we are very confident a performant onchain verifier could be written with mutability if it can be written at all. Our claim here gains further support from the fact that the Solidity implementation has been successfully deployed on the Ethereum mainnet and appears to function adequately in spite of the fact that it does not support very cheap reciprocals. Because we have access to very cheap reciprocals, it stands to reason that mutability would almost certainly suffice to address our performance issues. 

Unfortunately, mutability has one serious drawback: It is entirely unclear how it could be implemented in UPLC without extremely disruptive changes not just to the UPLC codebase, but also to the formal analyses and specification documents that support Plutus scripts. The primary reason is that UPLC simply lacks a rich enough type system to encode state threads using anything like the `ST` "trick" that is used in Haskell. The `ST` trick requires a type system that supports monads (or at least higher-kinded types with type variables and explicit quantification), and although UPLC is not quite as untyped as the name may indicate, its rudimentary type system is nowhere near expressive enough to use an analogous trick. Safety, therefore, would be the responsibility of UPLC frontend languages. While some frontend languages (e.g. Plutarch) may have a sufficiently expressive type system to represent mutation safely, others may not.

Lacking a type system that is sufficiently expressive to encode `ST` does not mean that mutability cannot be implemented, but it does strongly indicate that mutability cannot be implemented _safely_. As indicated above, UPLC only has a rudimentary type system that cannot represent local (i.e. "safe") mutability using anything like `ST`, and frontend languages would carry the burden of ensuring safety. It follows from this that UPLC itself would, out of necessity, have to expose unsafe primitives and builtins that support mutability. UPLC, therefore, would have to support global mutable state, which would have significant consequences for the language.

Moreover, we believe it is very likely that global mutable state would have severe and significant implications for the metatheoretical basis of the Plutus language and the consensus protocol, quite possibly in ways that make it difficult or impossible to prove certain important properties about the language or protocol. Of particular concern is the fact that the Ouruboros protocol relies (to a certain degree) on immutability in the script language. It may be possible to overcome those hurdles, however such a change would be incredibly disruptive and require a large amount of work, not just on UPLC itself, but elsewhere in the ecosystem. 


## Better Arrays 

The third option for modifying UPLC to support parametric onchain verification is to _improve the existing `Array` API_. 

At present, the default UPLC universe supports `Array`s (as a wrapper over strict `Data.Vector.Strict.Vector`s). UPLC also supports several basic operations, outlined in [CIP-138][CIP-138] provided as builtins: `LengthOfArray`, `ListToArray`, and `IndexArray`, which function as the names would indicate. 

The problem, for our purposes, with the existing `Array` API is not that it is defective, but rather that it is deficient: It lacks several essential operations which every other implementation of arrays (that we are familiar with) does not lack. In particular, the existing UPLC array API does not provide: 
  1. An efficient way to _construct arrays at runtime_. The existing API requires first constructing a list, and then converting to an array, which introduces nontrivial O(n) overhead. While the current API allows for lifting _array constants_ known at compile time, this is not particularly helpful because we must construct and modify arrays which can only be known at runtime. 
  2. A way to perform _updates_ that does not require a round trip through `List`. At present, to update an array element in UPLC, the only means available requires the following process: 
    - Convert the array `Array` to a `List` - there is no builtin function for this, but it can be done "manually" by determining the length and indexing the correct number of elements
    - _Then_ update the element or elements in the `List`, which (usually) requires a traversal of the elements
    - _Then_ covert the `List` back into an `Array`
  3. A way to slice or copy arrays efficiently 

No other language or library requires this much added computational complexity or syntactic clutter to work with arrays. Arrays are a fundamental data structure, and are the obvious and natural representation for the algorithms we are implementing here. Nearly every software developer is familiar with arrays and basic operations over them. These considerations constitute strong reasons for an improved `Array` API for Plutus, independent of the fact that they will likely solve our performance issues. That UPLC is a functional language should not preclude the possibility of performant arrays: Haskell's `vector` and `massiv` libraries both support efficient arrays in the context of a functional language. 

We believe it is very likely that a more robust `Array` API would allow us to implement performant addition and scaling. Again, a solidity example (this time of point addition) shows how these computations can be structured using arrays in a straightforward way, without exotic representations of datatypes or awkward continuation passing: 

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

Again, this Solidity implementation makes use of the Jacobian representation, and so would not translate directly for us. For a litany of reasons outlined in the [Milestone 3 report][M3], we believe that the affine representation is highly likely to be the most efficient representation under every modification of UPLC we are proposing here. However, as with the Solidity example from the previous section, the choice of representation is orthogonal to the ultimate cause of our performance problems. The reason is essentially the same: Mutability allows for caching the results of previous computations by storing them in a mutable variable, which eliminates the need for redundant over-evaluation when branching on the presence (or absence) of the point at infinity when examining the arguments. The difference between mutable variables and mutable arrays is largely stylistic, so an `Array` API which allows for efficient mutation would solve our problem just as well as fully realized mutability.  

There is, however, one seemingly obvious problem with proposing better `Array`s as a solution here: We have just said that only an `Array` that supports mutability would suffice, but the underlying `Vector` type for `Array` in `DefaultUni` is immutable! While adding mutable `Array`s to UPLC is possible, doing so is just as disruptive to the entire Plutus ecosystem as adding global mutable state would be. We are not suggesting that mutable `Array`s be added to the UPLC universe, because we do not think global mutable state is suitable for Plutus scripts, whether it takes the form of mutable variables or mutable arrays. 

Furthermore, we are aware that [considerations around costing higher order builtin functions][COSTING] prevent an enriched `Array` API from being implemented in the straightforward way: By "lifting" `Data.Vector` operations into `DefaultFun`. Because the (immutable) `Data.Vector` API does not - and cannot - expose an O(1) single element update function, but instead requires the use of higher order functions like `imap :: (Int -> a -> b) -> Vector a -> Vector b ` (and friends) to perform modifications as efficiently as possible, the impossibility of costing higher order builtins entails the need for a more sophisticated solution to the problem. 

Nonetheless, we believe that an improved `Array` API which supports _limited_ mutatability is likely the best option here. This solution is what we propose in the [MLabs Better Arrays proposal][BETTER_ARRAYS]. Our proposal, however, requires some explanation in the context of this report, because it is not a straightforward implementation of mutable `Array`s that readers might naively expect. Technically speaking, our proposal is a plan to implement one primitive "builder" type and several builtin operations that will allow us to use techniques such as (but not limited to) [defunctionalized push arrays][DEFUN-PUSH-ARRAYS] in a UPLC frontend language array API. 

Before explaining what our proposal is, and how it can give us restricted mutability without the issues that come with global mutable variables, we first have to explain (and explain the difference between) *pull arrays* and *push arrays*. Each representation has distinct advantage and disadvantages, and both are use internally by functional array libraries such as the previously mentioned `vector` and `massiv`. 

Pull arrays are one way of representing an array-like data structure in a functional programming context, and are supported by the [Plutarch][PLUTARCH] eDSL at present. Broadly speaking, pull arrays support reasonably performant implementations of several common operations over arrays. Specifically, `map`, `fold` and `slice` operations (and their common variants, e.g. indexed mapping) all have efficient implementations. While the actual Plutarch implementation uses a Boehm-Berarducci encoding for performance reasons, the basic idea is that arrays are represented with a datatype that is isomorphic to a partially instantiated `Store` comonad, a la: 

```haskell
data PullArray a = PullArray Int (Int -> a) 
```

Where the first argument to the constructor indicates the length, and the second argument is a function that produces an element when given an (in-bounds) index. Arrays are constructed by constructing an accessor function, and modified by composing other functions with the existing accessor function. 

Although pull arrays are an acceptable solution in contexts where only the subset of common array operations which have an efficient pull array implementation are needed, it is unfortunately common to require operations which do not have an efficient pull array implementation. Specifically, both indexing and single position modification are very costly, as is any transformation which modifies the number of elements (e.g. concatenation or appending). Unfortunately, this means that pull arrays will not solve our performance issues, because we require efficient indexing and updates. Readers can find a much more in-depth discussion of pull arrays, and their implementation in the Plutarch eDSL, in our [blog post][pull-arrays-blog-post]. 

Push arrays, like pull arrays, are a "deferred" representation of arrays, in that arrays are again encoded as functions that allow for the implementation of a basic array API. Push arrays are typically implemented using a code generation monad `CM` which can be "run" to produce a `Code` object the represents low-level operations over (mutable) arrays. A thorough explanation of push array implementations is beyond the scope of this report, but you can imagine that they are defined like so: 

```haskell
data PushArray a = PushArray (Int -> a -> CM ()) Int 
```

Where the function argument to the constructor represents a computation which produces a set of low level instructions when given an index and an element, and the `Int` argument represents the length. 

Push arrays allow for more efficient structural transformations (e.g. concatenation), support performant update operations for single elements, and (as with pull arrays) also support efficient `map` operations. This set of operations ought to suffice for us to implement performant curve point addition, particular for curves over higher order field extensions. Push arrays, therefore, would constitute an excellent choice for our purposes if they could be implemented in UPLC. 

Unfortunately, they cannot be implemented in UPLC in its current form in a manner that would be useful to us. There are two reasons for this: 

First, push arrays require a `Code` object that represents low-level (mutating) operations over arrays that the `CM` monad can produce when run. Because UPLC lacks efficient builtins for array operations, and because the `Code` object emitted by the `CM` monad can only be compiled into operations that actually exist, attempting to implement push arrays in UPLC would give us no real performance gains over the status quo. 

Second, because push arrays are a kind of DSL for describing the construction and modification of arrays, it is not obvious how they could be used at runtime. If suitable builtins existed, it might be possible to write a UPLC "runtime interpreter" for the DSL, but this would certainly add considerable overhead that would eliminate all of the gains we might otherwise enjoy from push arrays. 

We seem to be back where we started: Push arrays appear to require operations which would introduce global mutable state into Plutus scripts. However, there is another option, which we believe is the only sensible way to implement a richer array API, and which is not subject to the aforementioned problems. This is a solution which we propose in the [MLabs Better Arrays proposal][BETTER_ARRAYS]: Defunctionalized push arrays. 

The [MLabs Better Arrays proposal][BETTER_ARRAYS] can be understood as proposing an implementation of `CM` that works at compile time. Specifically, the core changes to UPLC we propose are: 
  - A polymorphic `ArrayBuilder` universe type  
  - A `CreateArrayBuilder :: Integer -> a -> ArrayBuilder a` builtin, which is used to describe computations that construct arrays 
  - A `WriteArrayBuilder :: ArrayBuilder a -> Integer -> a -> ArrayBuilder a` function for describing single element updates 
  - An `ArrayBuilderToArray :: ArrayBuilder a -> Array a` function which converts from the builder to the concrete array type 
  
It is important to be explicit that these additions to UPLC are not, on their own, an implementation of defunctionalized push arrays. As we state in our proposal, these builtins are intended for "internal" use by compilers of UPLC frontend languages. Should that proposal be funded, part of our work will be to modify the compilers for existing frontend languages, so that frontend languages only expose a safe interface which is then transformed into calls to these functions in a code transformation or code generation pass. These additions to UPLC, however, suffice for the implementation of arrays in a frontend language without directly exposing unsafe operations to users. While the exact shape of the frontend array API will require some research and experimentation, the better arrays proposal will give us access to the same low-level tools that libraries like `massiv` make use of to implement efficient arrays in a functional setting. 


[^1] Chris Okasaki, _Purely Functional Data Structures_, p.2

[^2] Specifically an indirect "on the outside", i.e. `ID`

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
