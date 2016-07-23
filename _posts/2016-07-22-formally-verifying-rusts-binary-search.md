---
layout: post
title:  "A Formal Verification of Rust's Binary Search Implementation"
date:   2016-07-22 14:47:00 -0400
---
This post is about my ongoing master's thesis under Jeremy Avigad at Carnegie Mellon University, in which I'm trying to tackle formal verification of Rust programs in the interactive theorem prover [Lean](http://leanprover.github.io/), and a first result of the project: a complete verification of the Rust stdlib's binary search function.

<div style="text-align: center" markdown="1">
[![Electrolysis logo](https://github.com/Kha/electrolysis/raw/master/logo.png?raw=true)](https://github.com/Kha/electrolysis)
</div>

# Putting the 'Formal' into 'Formaldehyde'

Formal Verification is the act of mathematically reasoning about a program's behavior. While there have been gargantuan verification projects like a [verified C compiler](http://compcert.inria.fr/) or a [verified microkernel](https://sel4.systems/) in the recent past, it is still mostly a research topic and is rarely being applied to programs that have not explicitly been written for verification.

Part of the reason for this is that it's quite complicated to apply mathematical tools to something unmathematical like a functionally unpure language (which, unfortunately, most programs tend to be written in).
In mathematics, you don't expect a variable to suddenly change its value, and it only gets more complicated when you have pointers to those dang things:

> "Dealing  with  aliasing  is  one  of  the  key  challenges  for  the verification of imperative programs. For instance, aliases make it difficult to determine which abstractions are potentially affected by a heap update and to determine which locks need to be acquired to avoid data races." [^1]

[^1]: Dietl, W., & Müller, P. (2013). Object ownership in program verification. In Aliasing in Object-Oriented Programming. Types, Analysis and Verification (pp. 289-318). Springer Berlin Heidelberg.

While there are whole [logics](https://en.wikipedia.org/wiki/Separation_logic) focused on trying to tackle these problems, a master's thesis wouldn't be nearly enough time to model a formal Rust semantics on top of these, so I opted for a more straightforward solution: Simply make Rust a purely functional language!

# Electrolysis: Simple Verification of Rust Programs via Functional Purification

If you know a bit about Rust, you may have noticed something about that quote in the previous section: There actually are no data races in (safe) Rust, precisely because there is no mutable aliasing. Either all references to some datum are immutable, or there is a single mutable reference. This means that mutability in Rust is much more localized than in most other imperative languages, and that it is sound to replace a destructive update like

```rust
p.x += 1
```

with a functional one -- we know there's no one else around observing p:

```rust
let p = Point { x = p.x + 1, ..p };
```

Likewise, we can turn a mutable borrow like

```rust
let x = f(&mut p) // f(&mut Point) -> A
```

into copying (or moving) the value, and copying it back when the borrow ends:

```rust
let (x, p) = f(p) // f(Point) -> (A, Point)
```

Just these rules are sufficient to make a big part of Rust programs functionally pure. There are obvious (borrowing a field) and non-obvious (returning a mutable reference) extensions to this basic idea, which I may discuss in a future post about what parts of Rust my project currently supports, what it may support in the future, and what it will never support.

I'm certainly not the first one to point out this semantics-preserving transformation -- see for example [this slide](http://asaj.org/talks/lola16/?full#refs:mutation-vr) by Alan Jeffrey from his talk at LOLA2016. But what I have used this realization for is to implement a [tool](https://github.com/Kha/electrolysis) that transpiles (a subset of) safe Rust into Lean, a purely functional language, in order to verify Rust programs with the same tools as ordinary definitions in Lean itself. This is what I call 'functional purification', and may excuse me reusing the name of an unrelated [Firefox project](https://wiki.mozilla.org/Electrolysis). After all, electrolysis is a chemical process that can be used for the purification of iron oxide (i.e., rust).

# Verifying the Correctness of `std::slice::binary_search`

So much for the theory for now, what does this look like in practice? For a first test, I decided to verify Rust's binary search function. It may not be the most interesting algorithm, but Rust's implementation is quite unique in that instead of using two simple indices like everyone else, it [uses](https://github.com/rust-lang/rust/blob/27e766d7bc84be992c8ddef710affc92ef4a0adf/src/libcore/slice.rs#L304-L324) high-level slice operations that let it circumvent bounds checking without resorting to unsafe code.
For my project, high-level means a dozen (indirect) dependencies and some advanced language constructs like traits, closures and pattern matching, which turned out to be a nice test case for the tool.

After about two weeks of working on the [proof](https://github.com/Kha/electrolysis/blob/asymptotic/thys/core/thy.lean#L121) (on second thought, don't look at that) and tweaking the transpiler in parallel, I managed to prove the following theorem:

<!-- unholy HTML code goes here -->
<pre class="emacs">
<span class="keyword">theorem</span> <span class="function-name">core.slice.binary_search.sem</span> : <span class="constant">&#8704;</span> <span class="rainbow-delimiters-depth-1">{</span>T : <span class="type">Type</span><span class="rainbow-delimiters-depth-1">}</span> <span class="rainbow-delimiters-depth-1">[</span>Ord' T<span class="rainbow-delimiters-depth-1">]</span>
  <span class="rainbow-delimiters-depth-1">(</span>self : list T<span class="rainbow-delimiters-depth-1">)</span> <span class="rainbow-delimiters-depth-1">(</span>needle : T<span class="rainbow-delimiters-depth-1">)</span>, sorted le self <span class="constant">&#8594;</span>
  option.any binary_search_res <span class="rainbow-delimiters-depth-1">(</span>binary_search self needle<span class="rainbow-delimiters-depth-1">)</span>
</pre>

Hey, don't run away just yet! Let me step you through it: This theorem says that given

* any type `T`
  * that implements some mysterious type class `Ord'`,
* any slice `self`
  * that is sorted according to `Ord'`
* and object `needle` of type `T`,

calling (the Lean translation of) `binary_search`

* terminates normally (in contrast to _abnormally_, i.e. panics, or not at all) with a value `some res`
* such that `binary_search_res res` is true (that's what the `option.any` is for).

The `binary_search_res` predicate is a 1:1 translation of `binary_search`'s [doc comment](https://doc.rust-lang.org/std/primitive.slice.html#method.binary_search):

<pre class="emacs">
<span class="keyword">inductive</span> <span class="function-name">binary_search_res</span> : Result usize usize <span class="constant">&#8594;</span> <span class="type">Prop</span> <span class="constant">:=</span>
<span class="comment-delimiter">-- </span><span class="comment">if the value is found then Ok is returned, containing the index of the matching element
</span>| found     : <span class="constant">&#928;</span>i, nth self i <span class="constant">=</span> some needle <span class="constant">&#8594;</span> binary_search_res <span class="rainbow-delimiters-depth-1">(</span>Result.Ok i<span class="rainbow-delimiters-depth-1">)</span>
<span class="comment-delimiter">-- </span><span class="comment">if the value is not found then Err is returned, containing the index where a matching
</span><span class="comment-delimiter">-- </span><span class="comment">element could be inserted while maintaining sorted order.
</span>| not_found : <span class="constant">&#928;</span>i, needle &#8713; self <span class="constant">&#8594;</span> sorted le <span class="rainbow-delimiters-depth-1">(</span>insert_at self i needle<span class="rainbow-delimiters-depth-1">)</span> <span class="constant">&#8594;</span>
    binary_search_res <span class="rainbow-delimiters-depth-1">(</span>Result.Err i<span class="rainbow-delimiters-depth-1">)</span>
</pre>

As an aside, if you look at (fully automated) verifications of binary search in other languages, you will find that these often concentrate on the first case, even though `not_found` is actually the more complex one, and only on the special case of integer arrays at that. This is where, in my view, interactive theorem provers really shine, by being able to use high-level abstractions like `sorted` or `insert_at` in specifications for arbitrary user-defined orders.

Which brings me to the last part, the `Ord'` type class, which [combines](https://github.com/Kha/electrolysis/blob/e9e7e804b6a824d83e127afee8c5e4416b1f5a52/thys/core/thy.lean#L33) the Rust `Ord` trait (that gets translated to a Lean type class) and the Lean `decidable_linear_order` type class, meaning implementations of the Rust trait must also fulfill the axioms of a linear order. Rust and Lean definitions, working together in harmony!

To conclude, given that the repo contains a machine-checked proof of this theorem, I hope you trust my assertion that `binary_search` is, indeed, correct! Well, by trusting me, you're more specifically trusting all of these parts:

* the Rust compiler, whose internal API my tool uses (mostly its excellent [mid-level IR](https://blog.rust-lang.org/2016/04/19/MIR.html))
* Lean itself
* my transpiler
* my [prelude](https://github.com/Kha/electrolysis/blob/master/thys/core/pre.lean) of language primitives
  * also contains manual translations of functions like `mem::swap` the transpiler doesn't like because they use unsafe code
    * there's also one slyly hiding in the [config file](https://github.com/Kha/electrolysis/blob/6930d87a7c042cbafae09f2bae7b20ef642e7af9/thys/core/config.toml#L31-L34)

So yes, the project does involve some non-negligible trust base. Still, I would argue that an error in any of these components is far more likely to prevent you from proving something that holds than to enable you to prove something that _doesn't_ hold.

The most likely kind of translation bugs may be not in the basic Rust semantics, but in representing side effects. Indeed, if you look at the prelude, you may notice that currently there's no modelling of overflows -- all integer types are unbounded on the Lean side. I'm still torn on this design issue, but tend to think that overflow checking is a poor fit for the kind of algorithmic verification proofs I'm striving for. It can generate very unintuitive preconditions ('you can't call `len()` on this recursive data structure for more than 2^64 elements') that may never be dispensed with because they depend on the program's input. In any case, overflow checking is not very interesting for the implementation at hand because every integer in there is trivially bounded by `self.len()`.

# Related Works

Reading 'Rust' and 'verification' in the title, you may first have thought of the [RustBelt](http://plv.mpi-sws.org/rustbelt/) project at MPI-SWS and wondered how the two projects relate to each other. As far as I know, the cornerstone of RustBelt will be a full formalized semantics of Rust -- exactly what I'm trying to avoid to do --, on top of which they will be able to reason about abritrary unsafe Rust code -- something that is an explicit non-goal of my project. Thus I feel like the two projects should complement each other quite nicely. At some point, you may even be able to use the RustBelt formalization to prove electrolysis's purification correct.

# (Speculating about) Future Work

I haven't decided yet what to prove next, which is the real reason I started writing this post: to get suggestions from the Rust community about code in or outside of `std` that may be interesting to verify, without using too many dependencies or crazy `unsafe` tricks. For example, a first candidate may be `sort`, but that one uses loads of unsafe code and the algorithm isn't even [that interesting](https://users.rust-lang.org/t/why-does-rust-use-mergesort-as-slice-sort-in-standard-library/6223/3) compared to implementations in other standard libraries. `binary_search` proved to be much more well-behaved in this regard.

Instead of avoiding code that does impure `unsafe` things, another approach would be to extend the transpiler so that it supports at least some well-behaved examples of impurity. Pointers aren't that bad, for example, as long as their use is localized to a single function. More generally, you may know that Haskell uses monads to tame both local (`ST`) and global (`IO`) impurity. Well, I'm already using the `option` monad to model non-termination. Replacing this monad with different ones (or whole monad stacks) may enable the transpiler to express more effects or other kinds of behavior like nondeterminism.

As a first simple example of this, I experimented with hiding a step counter inside the monad to [derive a bound](https://github.com/Kha/electrolysis/blob/144bc840ec35e5995166d6e5383dd434760f6197/thys/core/thy.lean#L429) on `binary_search`'s time complexity -- which turned out to be slightly more complex if you don't assume that comparisons will be constant-time and you don't have a model of Big O notation for multiparametric functions. But let me postpone discussing that to a potential future blog post instead of making this one even longer. Last time I checked, my university wasn't quite ready to accept theses in blog form yet.

# Discussions

[Rust Programming Language Forum](https://users.rust-lang.org/t/blog-post-a-formal-verification-of-rusts-binary-search-implementation/6644)

[Hacker News](https://news.ycombinator.com/item?id=12146049#12146807)

[r/rust](https://www.reddit.com/r/rust/comments/4u4hrl/a_formal_verification_of_rusts_binary_search)

---
