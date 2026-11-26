# Transport for MLTT supercompilation

This note records what a type-preservation theorem for a supercompiler on MLTT
has to mean.  The short version: it is a **transport theorem**, not a syntactic
same-type preservation lemma.

The current MLTT targets (`hard/mltt-j`, `hard/mltt-weaken`) prove source
typing facts.  They do not define reduction, definitional equality, or a
supercompiler, so the transport theorem below is a specification, not a result
already proved in this repository.

## 1. Why the naive statement fails

A supercompiler `sc` produces a residual program.  It does not produce a reduct
of the source term.  Therefore subject reduction does not apply:

```text
t : A
sc(t) : A'
```

`sc(t)` is not reached from `t` by `Step`.  Even when `sc(t)` is semantically
correct, its type may differ from `A` because supercompilation can:

- specialize an index term;
- reduce an index under a binder where the source reduction relation cannot;
- fold or generalize a term;
- change the evaluation context of a type index.

So the general statement

```text
Γ ⊢ t : A  ->  Γ ⊢ sc(t) : A
```

is false without a restriction on the supercompiler.

## 2. Three equality regimes

The replacement of `t` by `sc(t)` has three different meanings.

### Definitional equality

```text
A ≡ A'
```

Then `sc(t)` is already a term of `A` up to conversion, and ordinary dependent
substitution works.

### Propositional equality

```text
p : Id Ty A A'
```

Then `sc(t) : A'` must be transported:

```text
transport p sc(t) : A
```

The substituted program contains a transport.  This is the basic
**heterogeneous substitution** case.

### Semantic equivalence only

```text
A ~ A'
```

If no internal equality or equivalence-to-identity principle is available,
there is no syntactic substitution at all.  The comparison must be made in a
logical relation or a model:

```text
t ~ sc(t)  at  A ↦ A*
```

Plain MLTT does not make every equivalence an identity.  Univalence would turn
an equivalence into a transport path, but that is a stronger type theory than
the core formalised here.

## 3. Translation data

A typed supercompiler needs, at minimum:

```text
scTy  : Ty -> Ty
scCtx : Ctx -> Ctx
scTm  : Tm Γ A -> Tm (scCtx Γ) (scTy A)
```

It also needs a relation between source and residual contexts and types:

```text
ctxEq : Ctx -> Ctx -> Type
tyEq  : Ty -> Ty -> Type
```

with:

```text
ctxEq Γ (scCtx Γ)
tyEq  A (scTy A)
```

`ctxEq` and `tyEq` may be definitional equality, identity types, equivalences,
or a logical relation.  The theorem must state which one it uses.

If the supercompiler keeps contexts and types fixed, `scCtx` and `scTy` are the
identity, and the transport is trivial.  That is the restricted typed fragment.
It is not full supercompilation.

## 4. The transport theorem

The useful shape is:

```text
For every typed term
  Γ ⊢ t : A

there are
  eΓ : ctxEq Γ (scCtx Γ)
  eA : tyEq  A (scTy A)

and a transported term
  transport (eΓ, eA) (scTm t) : Tm Γ A.
```

If the context and type are definitionally unchanged, the transport is `refl`.

If they are propositionally equal, the transport is the identity eliminator.

If they are only semantically equivalent, the last line is not an internal
typing judgment; it is the term-level clause of a logical relation.

The theorem also needs **substitution naturality**:

```text
scTm (t[σ])  ≈  transport … (scTm t)[scSubst σ]
```

where `σ` is a context morphism and `scSubst σ` is its translation.  Without
this, the theorem does not compose across contexts and cannot justify replacing
a subterm inside a larger program.

## 5. What kind of substitution is this?

It is a **dependent substitution along a context and type translation**, not
ordinary capture-avoiding term substitution.

The operations involved are:

1. **Context morphism substitution**
   ```text
   σ : Δ -> Γ
   t[σ] : Tm Δ A[σ]
   ```

2. **Type-family transport**
   ```text
   P[t]  ->  P[sc(t)]
   ```
   If `t` appears in an index, replacing it changes the type family.  This needs
   a path or relation between `t` and `sc(t)`, not just a path between `A` and
   `A'`.

3. **Term transport**
   ```text
   sc(t) : A'  ->  transport eA sc(t) : A
   ```

4. **Substitution lemma**
   ```text
   t : A
   Γ, x : A ⊢ u : B
   --------------------------------
   Γ ⊢ u[x := t] : B[x := t]
   ```
   The translation must preserve this lemma, not merely the closed-term typing
   judgment.

The term `t` and its residual `sc(t)` have to be related in the same logical
relation that relates the types and contexts.  Type equality alone is not
enough when `t` occurs inside a type.

## 6. Structural requirements

A real transport theorem needs all of the following.

### Coherent transport

```text
transport refl t = t
transport (p · q) t = transport q (transport p t)
```

### Context extension

```text
ctxEq Γ Γ'  ->  ctxEq (A :: Γ) (A' :: Γ')
```

and similarly for every context former.

### Type-former congruence

For each type former `F`:

```text
tyEq A A'  ->  tyEq (F A) (F A')
```

with the computation rules preserved.

### Substitution stability

The translation commutes with substitution up to the chosen equality or
relation:

```text
scTm (t[σ])  ≈  (scTm t)[scSubst σ]
```

### Term-former congruence

Application, abstraction, case, roll, and the other term formers must preserve
the relation.  A supercompiler that folds only some formers is not covered.

### Universe and proof-irrelevance handling

If the supercompiler changes universe levels or proof terms, the transport
relation must account for cumulativity and proof irrelevance explicitly.

## 7. CwF / logical-functor formulation

The structural home for this is a **category with families** or a displayed
category:

- a context morphism is a substitution;
- a type is a family over contexts;
- a term is a section;
- transport is the action on a path/equivalence;
- the supercompiler is a functor between the source and residual models.

A type-preserving supercompiler is then a **logical functor** that preserves
context extension, type substitution, term substitution, and the type formers.
A supercompiler whose types change needs a **displayed** or **fibrational**
translation: the residual type lives over the translated context, and transport
is the Cartesian lift.

This is stronger than a collection of ad hoc preservation lemmas.  In
particular, it rules out a supercompiler that is correct on closed terms but
cannot be substituted into an arbitrary context.

## 8. Consequences for the MLTT targets

The current MLTT files have:

```text
Tm, Ctx, Env, IndSig, HasType
```

but no:

- `Step`;
- `Value`;
- definitional equality/conversion;
- general substitution;
- general weakening.

So the transport theorem is not yet statable for this formalisation.  The
prerequisites are:

1. reduction and conversion;
2. general weakening;
3. general substitution and context morphisms;
4. subject reduction;
5. progress;
6. strong normalisation and confluence;
7. a logical relation or contextual equivalence;
8. the supercompiler translation and its transport/equivalence proof.

The `J_has_type` and `Eq` weakening targets are useful proof-search benchmarks,
but they are below the transport theorem.  A full supercompilation theorem for
MLTT requires a theory of transport that is stable under substitution, not a
single type-preservation lemma.

## 9. Open question

The central design question is:

> Does the supercompiler preserve the source type up to internal equality, or
> does it translate types and require a logical relation?

If the answer is “internal equality”, the theorem can be syntactic and
transport is `J`.  If the answer is “types are translated”, the theorem is
semantic, and no amount of subject reduction or progress will replace the
missing transport/equivalence proof.

---

*Ported from `scidonia/proof-approach` (commit `4e1ba39`).  This file is the
problem statement for this repository; it is not a claim about what is already
mechanised.  See `docs/formalization.md` for the current Lean boundary.*
