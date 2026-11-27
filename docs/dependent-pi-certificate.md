# Certificates at a heterogeneous dependent function type

The nondependent `arr A A` certificate is the special case.  For a dependent
Π type the certificate is a **dependent function**, not a single relation on a
fixed result.

## The Pi clause

For source/residual types

```text
Π x : A.  B x
Π x' : A'. B' x'
```

and a type relation `TyRel`, the type relation at the Pi is:

```text
TyRel (Π x:A. B x) (Π x':A'. B' x')
  :=
  TyRel A A'
  ∧
  ∀ x x', LR_A(x,x') -> TyRel (B x) (B' x')
```

and a certificate for functions `f`, `g` is:

```text
PiCert f g
  :=
  ∀ x x', LR_A(x,x') -> LR_{B x, B' x'}(f x, g x')
```

The codomain relation is **indexed by the argument relation**.  The certificate
is a Π-type in the meta-logic: one certificate per related pair of indices.

- `A` and `A'` may differ.
- `B x` and `B' x'` may differ; the family relation relates them fiberwise.
- The **indices** are the arguments; a single `BisimRel` on a fixed result type
  cannot express this.
- The nondependent identity certificate at `arr A A` is the case where the
  family is constant and `x = x'`.

## Transport

A type equivalence

```text
e : (Π x:A. B x) ≃ (Π x':A'. B' x')
```

is fiberwise.  Transport along `e` must commute with application:

```text
transport e f x  ~  transport (fiber e x) (f x)
```

The family equivalence and the Pi equivalence are linked by this computation
rule.  A Pi certificate transports fiberwise; it is not a single path at one
point.

## Example: polymorphic identity

```text
id = λA. λx. x  :  Π A : Type. A -> A
```

The certificate is:

```text
∀ A A', LR_Type(A,A') ->
  ∀ x : A, x' : A', LR_A(x,x') -> LR_A(x,x')
```

The identity family is the fiberwise identity; the type argument is the index.
This is the simplest genuinely dependent Pi certificate.

## What the current code has

- `Transport/Closure.lean` has `Ty.arr` only; `identityLR` is the nondependent
  special case.
- `Transport/Mltt/Dependent.lean` has `HasTypeDep` with `pi`, `Eq`, and
  inductive families, but no conversion, reduction, or dependent logical
  relation.
- `Transport/ActionRel.lean` uses a **fixed** result relation
  `rel : S -> R -> Prop`; it cannot encode a Pi certificate, whose relation is
  a family over the argument relation.
- `Transport/FiberAction.lean` lifts the action calculus to a `FiberRel` family:
  `FiberBisim`, `FiberFoldCert`, `FiberGenCert`, and `FiberDerivation` are the
  per-index instances of the existing certificates.  It is not yet connected
  to the step-indexed object relation or to a Pi fold/generalisation.
- There is no object-language relation over the **core** `Tm` and no fiberwise
  transport theorem.
- There is a semantic `PiCert` over arbitrary index types, families, and
  fiberwise relations, with a polymorphic identity certificate `polyIdPiCert`
  in `Transport/DependentPi.lean`.
- There is a separate object syntax with a step-indexed `LR` in
  `Transport/DependentSyntax.lean`; `polyIdTyRel` and `polyIdTmRel` certify
  polymorphic identity at every step.
The first object-language attempt exposed two structural obstacles.

1. The core `Tm` is a **nested inductive**: `ind`, `roll`, and `case` carry
   `List Tm`.  `induction` does not support it directly, and proofs over its
   subterms need explicit recursive definitions.
2. A Pi relation written as an inductive has a **non-strictly-positive**
   occurrence: the Pi clause quantifies over all related arguments and then
   returns the relation at the codomain.  Lean rejects that inductive.

The object relation therefore needs either a separate dependent syntax or a
contextual definition, not an inductive over the core `Tm`.  The separate syntax
now uses **step-indexing**: the Pi clause is a recursive call at the previous
step, so the relation is a `def`, not an inductive.  This is the standard
step-indexed logical-relation trick; other routes are a greatest fixed point /
coinductive relation, an impredicative/Church encoding, or fuel on evaluation.
The semantic Pi certificate remains the checked dependent certificate.

## What is needed

1. A dependent type relation `TyRel` and term relation `LR` defined mutually,
   with the Pi clause above.
2. A `PiCert` carrying the dependent function of fiber certificates.
3. A type-indexed/fibered action interface; `BisimRel`/`DerivationRel` must be
   parameterised by the type relation, not a single result relation.
4. Fiberwise transport/`ua` coherence for the Pi type.
5. A concrete polymorphic identity or `Vec`/`Fin` family certificate.

The first target is the polymorphic identity because it exercises a type index,
a function-space fiber, and the dependent Pi clause without requiring a
recursive family.  That target is now checked semantically; the object-language
Pi and the fibered action interface are the next steps.
