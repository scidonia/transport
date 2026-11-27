# A certified supercompiler

The transformation should produce a residual program together with a proof term
that the residual is equivalent to the source at the source type.  The proof
term is checked by Lean; the oracle is not trusted.

This note fixes the certificate objects and the first build order.

## 1. The correctness statement

For a source `t : A`, the transformation returns

```text
A' : Type
e  : A' ≃ A
r  : Term A'
cert : LR_{A' ~ A}(r, t)
```

with the final theorem

```text
transport e r ≡ctx t : A
```

`LR` is the heterogeneous typed logical relation.  The certificate is a term of
`LR`; it is not a proposition asserted by the compiler.

## 2. Certificate objects

### 2.1 Generalisation certificate

A generalisation is a **schema**, not an equivalent term at the same type:

```text
structure GenCert (t : Term Γ A) where
  schema : Term Δ B
  inst   : Subst Δ Γ
  sound  : LR_{Γ,A}(t, schema[inst])
```

The generalised term may be polymorphic, higher-order, or a worker over extra
parameters.  The certificate proves the particular instantiation is related to
the source.

- **Algorithmic generalisation**: anti-unification or a similar procedure
  constructs `schema` and `inst`, and the `sound` proof is by reflexivity,
  definitional equality, or a type-directed argument.
- **Oracular generalisation**: the oracle returns `schema`, `inst`, and a proof
  term for `sound`.  The kernel checks the proof.  An oracle that returns only
  a term or a proposition, without a proof, is not accepted.

The certificate is a **proof step**: the supercompiler may choose not to
generalise, but if it does, the `GenCert` is part of the derivation.

### 2.2 Fold certificate

A label is a recursive definition.  Replacing a term by a label is justified by
the equation between the term and the **unfolding** of the label:

```text
structure FoldCert (t : Term Γ A) (label : Label Γ A) where
  unfold  : Term Γ A
  equation : unfold = label.unfold
  bisim   : Bisim_A(t, unfold)
  guarded : Guarded(label)
```

- `unfold = label.unfold` is definitional when the label is a `letrec`/fixed
  point; the proof is the unfolding equation.
- `bisim` is the behavioural certificate: a bisimulation or a step-indexed
  logical relation at `A`.
- `guarded` is the productivity/termination certificate for the recursive
  label.

A fold is a **coinductive** step.  If the residual language has general
recursion, `Bisim` is a greatest fixed point; if the language is total, it can
be step-indexed (`Bisim n` for all `n`) or guarded by a termination measure.

### 2.3 Step and residual certificates

```text
structure StepCert (c c' : Config) where
  sound : LR(c, c')
```

The residual derivation is a sequence/cycle of `StepCert`s.  A fold closes a
cycle with a `FoldCert`; a residualisation closes with the source certificate.
The final `ResidualCert` is the composition.

## 3. The logical relation

`LR` must be:

- heterogeneous: `LR_{A~A'}` for source/residual types related by a type
  equivalence/path;
- type-directed: clauses for `Pi`, `Sigma`, identity, inductive families,
  universes;
- stable under substitution, weakening, and conversion;
- adequate for typed contextual equivalence (or CE after transport);
- extended coinductively/step-indexed for recursive labels.

For a total fragment, a step-indexed relation is practical in Lean:

```text
∀ n, LR_n(t, u)  =>  t ≡ctx u
```

The fold certificate is a bisimulation in `LR_n`; the guardedness proof ensures
the label is productive.

## 4. Generalisation as a proof step

The supercompiler's generalisation phase has two modes:

1. **Algorithmic**: a deterministic procedure (anti-unification, most specific
   generalization, a heuristic) returns `schema`, `inst`, and a proof.
2. **Oracular**: an external oracle returns the same data plus a proof term.

The difference is **who finds the proof**, not whether a proof exists.  The
checker accepts the `GenCert`; the oracle cannot assert an unproved equivalence.

This is the right place for the "equivalences between terms" used in
supercompilation: they are not syntactic rewrites, they are `GenCert` proofs at
the type relation.

## 5. How to prove a label equivalence

There are three cases.

### 5.1 Definitional label

If `label` is defined as `t` (a `letrec`, a local definition, a worker whose
unfolding is `t`), the equivalence is the unfolding equation.  No behavioural
proof is needed; the label is notation for the term.

### 5.2 Generalised label

If the label is a generalised worker and `t` is an instance, the proof is the
`GenCert` plus the instantiation:

```text
LR(t, schema[inst])
```

The reverse example is exactly this: `revAcc xs a` is generalised over the
accumulator `a`, and `derivation_sound xs a` is the certificate for every
instance.

### 5.3 Behavioural label

If the label is not definitionally the term, prove a **bisimulation**:

```text
R = { (t, unfold label) } ∪ ...
```

and show `R` is closed under steps and observations.  The greatest
bisimulation/step-indexed relation is contained in contextual equivalence by
adequacy.  This is the general case; a fold is a coinductive proof.

A pure untyped equivalence is not enough: it forgets the type relation and the
function-type clauses.  The label equivalence is a typed `LR`/bisimulation.

## 6. Folds are the hard part

A fold is not just a recursive call; it introduces a **cycle** in the residual
program.  The obligations are:

1. **Unfolding**: the label's unfolding is the configuration/term it replaces.
2. **Bisimulation**: the source and the unfolding are related at the type.
3. **Guardedness**: the recursive label is productive/terminating; otherwise the
   residual program may diverge where the source does not.
4. **Composition**: the bisimulation composes with the surrounding residual
   context; the logical relation is a congruence (adequacy).
5. **Whistle/termination**: the supercompiler only folds when the label is already
   present and the generalisation/fold certificate is valid; the process graph
   must be finite or the residualisation must be justified.

The fold certificate bundles 1--3.  The final residual certificate composes it
with the step certificates.

## 7. Build order

### Stage 0: the existing reverse derivation

`Transport/Derivation.lean` already contains a first-order certified worker:

- the generalized worker is `revAcc xs a` (generalised over `a`);
- the recursive edge has a decrease proof (`Edge.fold_decrease`);
- the residual theorem is `derivation_residual`;
- the base logical relation is equality of `List` denotations.

This is a `GenCert`-style proof (generalisation over `a`) and a recursive
worker, but the "fold" is not a distinct label/letrec edge and the relation is
denotational equality, not a step-indexed `LR`.

### Stage 1: a labeled process calculus — first instance checked

`Transport/Certified.lean` now has:

- a residual label `rev`;
- a labelled step relation and a fuel-indexed `run`;
- a fuel-indexed bisimulation `Bisim n c` agreeing with `revAcc`;
- `FoldCert` with the label step, unfolding, bisimulation, and guarded decrease;
- `reverseFold` for a nonempty reverse configuration;
- `run_sound` and `residual_sound`.

This is a real label and a proof-carrying fold, but the label's semantics is the
same worker: the next refinement is a residual language where the label is an
independent recursive definition and `Bisim` is a step-indexed relation between
two configurations, not just the label against the worker.

### Stage 2: `GenCert`

Add the `GenCert` structure and an algorithmic anti-unification instance.
For the reverse worker, generalisation over the accumulator is the first
instance; the soundness proof is the existing universal theorem.

### Stage 3: a simple supercompiler

Implement driving, generalisation, folding, and residualisation for the
first-order fragment.  Each step returns its certificate; folds use
`FoldCert`; generalisations use `GenCert`; the residual derivation composes
them.

### Stage 4: the typed relation

Replace the denotational base relation with the heterogeneous typed `LR` and
the step-indexed/coinductive extension.  Then the certificate is the typed
logical relation, and the final theorem is transport + contextual equivalence.

## 8. Status

This note is a design and a build order.  The repository currently has the
Stage 0 worker, but not the labeled process calculus, `GenCert`/`FoldCert`, a
step-indexed bisimulation, a typed `LR`, or a general supercompiler.  The T1--T10
obligations in `docs/equivalence.md` remain the acceptance criteria.
