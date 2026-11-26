# Dependent basis: the metatheory a full supercompiler needs

The transport theorem is the correctness condition for a supercompiler on
Martin-Löf type theory.  It is not the supercompiler.  This note records the
metatheory that a full dependent supercompiler requires, what the current
development has, and the order in which the missing layers are built.

## 1. The gap in the indexed core

`Transport/Mltt/Core.lean` fixes the syntax, renaming, substitution,
signatures, and the typing judgment.  Its indexed rules use `substMany`:

```text
ind I args       : substMany args (substParams params (Ty I))
roll I c args    : substMany args (ctor type)
case I n ...     : substMany args (substParams params (branch type))
```

`substMany xs t` replaces variables `0 .. xs.length - 1`.  Renaming commutes
with it only when every free variable of `t` is below `xs.length`:

```text
substMany (xs.map (rename ρ)) t = rename ρ (substMany xs t)
```

The current `IndSig` has no such bound on its parameter, index, or constructor
types.  General weakening therefore cannot be proved for the `ind`, `roll`,
and `case` rules, and the existing weakening proof is specialised to the `Eq`
signature.  This is the first obstruction to the full basis.

## 2. What is in place

`Transport/Mltt/Scoped.lean` introduces the missing notion of scope:

* `WellScoped d t` is an inductive predicate: every free variable of `t` is
  below `d`; the depth increases under `pi`, `lam`, and `fix`, and the `case`
  motive is scoped at `d + n + 1` because it binds the `n` indices and the
  scrutinee.
* `rename_upRenN_of_wellScoped` proves that the identity renaming below the
  depth fixes a well-scoped term.
* `upRenN_add` proves the composition law for the depth renaming used by the
  `case` motive.
* `WellFormedSig` and `WellFormedEnv` state the telescope invariant for
  signatures and environments; `eq_sig_wellFormed` and `wellFormedEnv_Eq`
  verify it for the `Eq` signature and its environment.
* `substMany_rename_of_wellScoped` commutes renaming with `substMany` when
  the substituted term is scoped by the substitution length.

The signature invariant is proved for `Eq`, but it is not yet used by a
general weakening proof; that proof is the next stage and will test the
invariant for arbitrary signatures.

## 3. The staged basis

| stage | target | depends on |
| --- | --- | --- |
| B1 | well-scoped terms; identity renaming below the depth | done |
| B2 | `WellFormedSig` for the `Eq` signature and its environment | B1 |
| B3 | `substMany_rename` under a scope bound | B1 |
| B4 | general weakening and substitution for the full `HasType` | B2, B3 |
| B5 | context morphisms; `caseMotiveCtx` commutation | B4 |
| B6 | conversion and definitional equality; conversion is a congruence | B4 |
| B7 | subject reduction for beta, `J`, and `case` | B5, B6 |
| B8 | progress for the total fragment | B7 |
| B9 | strong normalisation and confluence | B7 |
| B10 | logical relation or contextual equivalence | B8, B9 |
| B11 | supercompiler translation and its transport theorem | B10 |

B4 is the immediate target, but it is not a direct patch to the existing
`Weaken.lean`; section 4 records the two core limitations.  B5 is where the
`case` motive's context extension has to commute with weakening.  B6--B10 are
the object-theory metatheory.  B11 is the supercompiler itself.

## 4. B4 obstruction in the current core

A direct general weakening proof is blocked by the shape of the current
typing rule, not only by missing lemmas.

1. The original `HasType.case` requires `ctor.paramTys = []` and
   `ctor.recArgs = []`.  The branch is therefore checked in the original
   context `Γ`, and the branch type is just the motive at the constructor's
   nullary result.  `Transport/Mltt/Dependent.lean` now supplies the general
   rule as a separate relation `HasTypeDep.caseDep`: the branch context is
   the constructor telescope `Δ_i`, and the branch result is the motive at
   the constructor's result indices and the `roll` term.  The old `HasType`
   is unchanged, so its existing proofs still hold; the new relation is not
   yet used by the transport theorem.
2. `caseMotiveCtx` uses `ctxExtendMany`, which shifts each type as it adds
   the next index.  The weakening renaming for a multi-index motive is
   therefore not a single `upRenN`; it depends on the position in the
   telescope.  The `Eq` proof works around this with `caseMotiveCtxEq`,
   specialised to `params.length = 2` and a one-index family.  A general
   proof needs either a telescope predicate with a context-morphism lemma,
   or a context representation that does not shift the tail.

The next stage is therefore:

1. ~~add a dependent `case` rule~~ — done in `Transport/Mltt/Dependent.lean`
   as `HasTypeDep.caseDep`, separate from the old `HasType`;
2. define a well-scoped telescope context and prove weakening and
   substitution for `HasTypeDep`;
3. then relate `HasTypeDep` to the old judgment and return to B4.

The checked B1--B3 layer remains useful: it supplies the scope predicate
and the `substMany` commutation the new case rule needs.

## 5. Scope of the checked layer

The checked theorems are B1--B3:

```text
Transport.Mltt.Scoped.rename_upRenN_of_wellScoped
Transport.Mltt.Scoped.eq_sig_wellFormed
Transport.Mltt.Scoped.wellFormedEnv_Eq
Transport.Mltt.Scoped.substMany_rename_of_wellScoped
```

They say that a term scoped by `d` is fixed by the identity renaming below
`d`, that the `Eq` signature and its environment satisfy the telescope
invariant, and that renaming commutes with `substMany` for scoped terms.
They do not say that weakening holds for an arbitrary well-formed
environment, that conversion is stable, or that a supercompiler exists.
The dependent case relation `HasTypeDep.caseDep` is a rule, not a weakening
theorem: its metatheory is still open.  Those statements are stages B4--B11
above, and each needs its own proof.

## 6. Why this order

The supercompiler's residual program lives in a translated context.  Before
the translation can be typed, the object theory must have:

1. a well-formed context and signature invariant;
2. general renaming and substitution;
3. a conversion relation that is stable under those operations;
4. subject reduction for the steps the supercompiler performs.

Only then can a logical relation relate source and residual programs, and only
then can the transport theorem be instantiated at the supercompiler's
translation.  Proving the supercompiler first would leave the type-preservation
claim without the lemmas it needs.

## 7. Relation to the transport theorem

`Transport/Spec.lean` states the transport data and the theorem schema.  The
definitional instance and the beta instance are checked.  The indexed and
dependent instances await B4--B7.  The Cubical Agda development supplies the
univalent/type-level packing used by the HoTT interpretation; it is not a
replacement for the object-theory metatheory.

The dependent case rule is now present.  The next concrete milestone is
weakening and substitution for `HasTypeDep`, using the telescope branch
context; B4 follows once that relation is related back to the old judgment.
