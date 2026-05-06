# EL2

The goal of this project is to implement minimal dependent type checker. Currently, it should be able to handle Calculus of Constructions (CoC) with Type universes. Next goal, fully Calculus of Inductive Constructions (CIC) just like lean4 or rocq

![example.el2](https://raw.githubusercontent.com/fbundle/el2/refs/heads/master/screenshots/screenshot2.png)

## TODO

pattern matching as syntactic sugar

```lean
inh Nat : Type0
inh zero : Nat
inh succ : Nat -> Nat

inh nat_rec :
  (P : Nat -> Type0) ->
  (P zero) ->
  ((n : Nat) -> (P n) -> (P (succ n))) ->
  (n : Nat) -> (P n)
```

then 
```lean
match n with
| zero => a
| succ m => b m
```

is equivalent to
```lean
nat_rec (λ _. T) a (λ m rec. b m) n
```

## TYPE CHECKING WITH COQUAND'S ALGORITHM

It is a difficult topic checking of an inductive type is well-defined or at least positive recurrent.

There are two main ways to typecheck inductive types: (1) using fixpoint combinator which is not decidable and (2) using the initial object $\mathbb{N}$ of the category $F$-algebras over the category of sets where $F(X) = 1 + X$ where $1$ is the singleton set and $1 + X$ is the disjoint union.

Both of which are not a simple weekend project, hence I decided to stop here. Currently, we simulate inductive types using `*` operator (or `inhabit`) which basically assume some type inhabits. 

The example above assumed `Nat` is a constant of type `type_0`, `zero` is a constant of type `Nat`, `succ` is a function `Nat -> Nat`, etc.

The original Coquand's algorithm can be found in `obsolete/coquand/1-s2.0-0167642395000216-main.pdf`, the implementation in Haskell is at `obsolete/coquand/app/Main.hs`, the implementation in Lean4 is at `obsolete/Coquand.lean`

I respectively added type universes, inhabit, annotated type, and desugaring for application of untyped lambda.

## PARSER COMBINATOR

Parser Combinator is a procedure to write parser

one of the best tutorial out there from tsoding [https://youtu.be/N9RUqGYuGfw](https://youtu.be/N9RUqGYuGfw)

## SOME WORDS ON TACTIC MODE AND INTERACTIVE THEOREM PROVER

### ON THE SOUNDNESS OF EL2

with the introduction of `inh` (called inhabit), one can introduce any axiom even if they are wrong. the system is sound with respect to its set of axioms

### TACTIC MODE

tactic is a useful tool for interactive theorem prover / backward reasoning. For example, we can prove `A ∧ B → B ∧ A` as follows:

```
> new A ∧ B → B ∧ A

⊢ A ∧ B → B ∧ A
> intro

0: A ∧ B
⊢ B ∧ A
> constructor

0: A ∧ B
⊢ B
> cases 0

0: A ∧ B
1: A
2: B
⊢ B
> exact 2

0: A ∧ B
⊢ A
> cases 0

0: A ∧ B
3: A
4: B
⊢ A
> exact 3

-- all goals accomplished!
```

One can also implement tactics in CIC and encode logic into CIC (this is what theorem provers use to encode mathematics into their type theories: dependent types, universes, recursive types, etc). An example of tactic we can implement for EL2 is as follows

```el2
Bool: Type0
true: Bool
false: Bool
Vec : hom Nat Type0 -> Type0
nil : hom (T: Type0) -> (Vec zero T)
push : hom (n: Nat) (T: Type0) (v: (Vec n T)) (x: T) -> (Vec (succ n) T)

⊢ (Vec 3 Bool)    -- goal: construct a vector of 3 booleans

> compose push    -- compose with push
```

split into 4 subgoals and 1 compose subgoal

```el2
...
⊢ Nat             -- value of n (should be 2)
```

```el2
...
⊢ Type0           -- value of T (should be Bool)
```

```el2
...
⊢ (Vec n T)       -- value of (Vec n T) (should be a vector of 2 booleans)
```

```el2
...
⊢ T               -- value of x (should be the tail of the goal vector)
```

```el2
...
⊢ (Vec (succ n) T) = (Vec 3 Bool)    -- a proof for these two types being identical
```

this is how we construct `Vec 3 Bool` backward

### ENCODE PROPOSITION LOGIC INTO EL2

since we can encode inductive types into `EL2`, propositional logic follows

```el2
let False: Type0

let And: (L: Type0) (R: Type0) -> Type0
let and_intro: hom (L: Type0) (R: Type0) (l: L) (r: T) -> (And L R)
let and_elim_left: hom (L: Type0) (R: Type0) (x: (And L R)) -> L
let and_elim_right: hom (L: Type0) (R: Type0) (x: (And L R)) -> R

let Or: (L: Type0) (R: Type0) -> Type0
let or_intro_left: hom (L: Type0) (R: Type0) (l: L) -> (Or L R)
let or_intro_right: hom (L: Type0) (R: Type0) (r: R) -> (Or L R)
let or_elim: hom (L: Type0) (R: Type0) (Y: Type0) (l: L -> Y) (r: R -> Y) (x: (Or L R)) -> Y
```

