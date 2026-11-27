# The general transport theorem

This note states the general transport theorem for a typed supercompiler,
independently of any particular supercompiler or example.

## Data

A translation is

```text
scCtx : Ctx -> Ctx
scTy  : Tm  -> Tm
scTm  : Tm  -> Tm
```

A `TransportData` supplies proof-relevant relations

```text
ctxRel : Ctx -> Ctx -> Type
tyRel  : Tm  -> Tm  -> Type
```

and an operation

```text
transport : ctxRel Γ Γ' -> tyRel A A' -> Tm -> Tm
```

with soundness

```text
Γ' ⊢ t : A'
ctxRel Γ Γ'
tyRel A A'
------------------------------
Γ ⊢ transport t : A
```

The relations are `Type`-valued.  A certificate is data: two transports with
the same endpoints can carry different substitutions or migration maps.  Only
soundness is a proposition.

## One-stage theorem

```lean
theorem transport_along (td : TransportData)
    (hΓ : td.ctxRel Γ Γ') (hA : td.tyRel A A')
    (ht : HasType env Γ' t A') :
    HasType env Γ (td.transport hΓ hA t) A
```

This is the general form of the theorem.  The definitional, propositional, and
semantic regimes are different instances of `ctxRel`, `tyRel`, and
`transport`; they are not different composition arguments.

## Two-stage composition

For two supercompilers and their transport data:

```text
Γ ⊢ t : A
  -- sc₁ -->  Γ₁ ⊢ sc₁t : A₁
  -- sc₂ -->  Γ₂ ⊢ sc₂(sc₁t) : A₂
  -- td₂ -->  Γ₁ ⊢ ... : A₁
  -- td₁ -->  Γ  ⊢ ... : A
```

The formal theorem is `Transport.transport_theorem_comp`:

```lean
td₁.transport (hctx₁ Γ) (hty₁ A)
  (td₂.transport (hctx₂ (sc₁.scCtx Γ)) (hty₂ (sc₁.scTy A))
    (sc₂.scTm (sc₁.scTm t)))
```

It is proved by composing the two soundness fields after the two typing
directions.

## The three regimes

| regime | `ctxRel` / `tyRel` | transport |
| --- | --- | --- |
| definitional | equality of syntax | identity / `refl` |
| propositional | a proof-relevant identity witness | identity eliminator |
| semantic | a logical relation or equivalence | a logical-relation clause |

The theorem is uniform over the regime because the regime is a choice of
`transport` and its soundness proof, not a change to the composition.

## Coherence obligations

The theorem is a schema.  A supercompiler instance is expected to satisfy:

```text
transport (refl Γ) (refl A) t = t
transport (comp h₁ h₂) (comp k₁ k₂) t
  = transport h₁ k₁ (transport h₂ k₂ t)
```

and the congruence/substitution laws:

```text
transport (ctxExtend h) (tyFormer k) (t[σ]) 
  ≈ (transport h k t)[scσ]
```

The general composition theorem does not prove these for an arbitrary
supercompiler.  The substitution square is formalised separately: a
`TransportData.Subst` supplies `ctxSubst`, `tySubst`, and `transport_subst`,
and `transport_subst_typing` reads a substituted residual term back at the
substituted source context and type.  The equation is an explicit coherence
field, not a theorem for an arbitrary supercompiler.

In the current development:

- `TransportData.identity` is the definitional instance;
- `Transport.BetaInstance` is a non-identity instance on the simple fragment;
- substitution stability for a general supercompiler is still open;
- the semantic regime is represented by the fibered logical relation, not by a
  general `TransportData` instance.

## Displayed-functor reading

A category with families has a base of contexts, a presheaf of types, and a
presheaf of terms.  A supercompiler is:

- a functor on the base: `scCtx`;
- a displayed functor on types: `scTy`;
- a displayed natural transformation on terms: `scTm`.

Transport is the Cartesian lift of the displayed morphism.  The three regimes
are three ways the lift can be computed: by `refl`, by `J`, or by a logical
relation.  The general theorem says that any such lift with the soundness
property composes; it does not claim that a given supercompiler has one.
