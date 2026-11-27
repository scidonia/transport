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
- There is no object-language `TyRel`/`LR` over dependent types and no fiberwise
  transport theorem.
- There is a semantic `PiCert` over arbitrary index types, families, and
  fiberwise relations, with a polymorphic identity certificate `polyIdPiCert`
  in `Transport/DependentPi.lean`.
- The object-language `LR` is a **canonical value** relation: it has clauses for
  sorts, Pi types, and lambdas, but no application, reduction, or operational
  step.  It is a first object-language certificate, not yet the full action
  interface.

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
