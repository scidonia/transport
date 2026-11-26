# Formalisation map

This page records what the Lean development actually contains, which hypothesis
each theorem needs, and where the boundary of the mechanised result is.  The
problem statement is [transport-mltt.md](transport-mltt.md); the paper plan is
[paper.md](paper.md).

## Build and trust

```bash
nix develop -c lake build
```

The development has no `sorry`, no `admit`, no `native_decide`, and no new
`axiom`.  `#print axioms` on the new theorems reports `propext` and
`Quot.sound` only, the same footprint as the ported proofs.

## The object theory

`Transport/Mltt/Core.lean` fixes:

- `Tm` with `var`, `sort`, `pi`, `lam`, `app`, `fix`, `ind`, `roll`, `case`;
- `Ctx = List Tm` with shift-aware lookup and telescope extension;
- `IndSig`, `CtorSig`, strict positivity, `lookupIndStrict`;
- `HasType env Γ t A`, including the index-refining `case` rule and the
  `substMany` side conditions for `ind`, `roll`, and `case`.

`Transport/Mltt/J.lean` proves `J_has_type_proof`: the `Eq` eliminator
typechecks with the index-refining case rule.

`Transport/Mltt/Weaken.lean` proves `hasType_weaken_proof`: adding an unused
context binder shifts the term and its type and preserves typing, for the `Eq`
family.  It also contains the general renaming algebra (`rename_comp`,
`rename_subst`, `subst_rename`, `rename_substMany`, `Wk`, `Wk_extend`) that the
rest of the development reuses.

## The fragment

The general `HasType` rules for `ind`, `roll`, and `case` compute types by
`substMany`, and the stored signature types do not carry a free-variable bound.
The commutation `rename ρ (substMany args t) = substMany (args.map ρ) ...`
therefore needs a well-formedness condition that the current signature
representation does not provide.  That is why general weakening is open.

`Transport/Mltt/Subst.lean` isolates the algebra that does not depend on the
inductive families:

| theorem | statement |
| --- | --- |
| `rename_id` | `Tm.rename id t = t` |
| `subst_var` | `Tm.subst Tm.var t = t` |
| `subst_subst` | substitution composition |
| `subst_subst0` | `subst σ (subst0 u B) = subst0 (subst σ u) (subst (upSub σ) B)` |
| `upSub_comp` | `upSub` commutes with composition |
| `subst_upSub_shift` | `subst (upSub σ) (shift 1 0 A) = shift 1 0 (subst σ A)` |

`Simple` is the predicate for `var`, `sort`, `pi`, `lam`, and `app`.  It makes
the impossible `ind`/`roll`/`case` cases of the typing induction vacuous.

`Transport/Mltt/Fragment.lean` proves, under `Simple t`:

| theorem | statement |
| --- | --- |
| `hasType_rename_simple` | a `Wk` renaming preserves typing |
| `hasType_subst_simple` | a context morphism `σ` preserves typing and its result type |
| `hasType_subst0_simple` | single substitution at the app rule's result type |

## Beta

`Transport/Mltt/Beta.lean` defines the outermost-redex contraction

```lean
def beta : Tm → Tm
  | .app (.lam _ body) arg => Tm.subst0 arg body
  | t => t
```

and proves `beta_preserves_hasType`: for a simple term, a typing derivation is
preserved by contraction.  The proof is the substitution lemma at the app
rule's result type.  This is a non-identity translation, so it is the first
concrete instance of the transport theorem rather than the identity instance.

## Orbit connectivity

`Transport/Orbit.lean` supplies the component theorem and the beta baseline.

- `iter f n x` is the `n`-fold forward iterate (defined locally; Lean core does
  not export the iterate API on this toolchain).
- `OrbitConnected f p q` is `∃ m n, iter f m p = iter f n q`.
- `orbitConnected_equivalence` proves it is an equivalence for any endofunction,
  including one with infinite orbits.
- `not_orbitConnected_of_fixed_ne` separates distinct fixed points.
- `BetaInstance.identityTm` is `λx. x` and `BetaInstance.redexUnderBinder` is
  `λx. (λy. y) x`; both are typed at `pi (sort 0) (sort 0)`.
- `typed_fixed_points_disconnected` proves they are in different `beta`
  components, and `typed_fixed_points_connected_after_binder` proves the binder
  rule `betaBinder` connects them.

This is a statement about the endofunction graph, not a reduction relation on
the full indexed syntax.

## The transport theorem

`Transport/Spec.lean` fixes the interfaces.

```lean
structure Translation where
  scCtx : Ctx → Ctx
  scTy : Tm → Tm
  scTm : Tm → Tm

structure TransportData where
  ctxRel : CtxRel
  tyRel : TyRel
  transport : ∀ {Γ Γ' : Ctx} {A A' : Tm},
    ctxRel Γ Γ' → tyRel A A' → Tm → Tm
  sound : ∀ {env : Env} {Γ Γ' : Ctx} {A A' : Tm} {t : Tm}
    (hΓ : ctxRel Γ Γ') (hA : tyRel A A'),
    HasType env Γ' t A' → HasType env Γ (transport hΓ hA t) A

structure Supercompiler where
  translation : Translation
  ctxRel : CtxRel
  tyRel : TyRel
```

The relations are `Type`-valued: the chosen substitution or migration map is
data, and two certificates with the same endpoints can differ.  `sound` stays
in `Prop`.

`transport_theorem` composes a `Supercompiler` with a `TransportData`:

```lean
theorem transport_theorem
    (sc : Supercompiler) (td : TransportData)
    (hctx : ∀ Γ, td.ctxRel Γ (sc.translation.scCtx Γ))
    (hty : ∀ A, td.tyRel A (sc.translation.scTy A))
    (htm : ∀ {env : Env} {Γ : Ctx} {t A : Tm},
      HasType env Γ t A →
      HasType env (sc.translation.scCtx Γ)
        (sc.translation.scTm t) (sc.translation.scTy A)) :
    ∀ {env : Env} {Γ : Ctx} {t A : Tm}, HasType env Γ t A →
      HasType env Γ
        (td.transport (hctx Γ) (hty A) (sc.translation.scTm t)) A
```

`transport_theorem_fragment` is the same statement with the additional
`Simple t` hypothesis, which is the current boundary.

`TransportData.identity` is the syntactic-equality regime: `ctxRel = Eq`,
`tyRel = Eq`, `transport = fun _ _ t => t`, and `sound` is `Eq.rec`.
`Transport.BetaInstance.transport` instantiates the fragment theorem at beta contraction.

Beta is deliberately a **term-level** translation, not a compositional one.
Substituting a lambda for a variable can expose a redex that `beta` did not
see, so `beta (t[sigma])` and `(beta t)[sigma]` are not equal in general.
`Transport.BetaInstance.transport` is therefore an instance of the basic fragment theorem,
not of the substitution-natural theorem of §4.1 of the problem statement.  The
distinction is the point: a supercompiler can be type-preserving on a closed
derivation and still fail to compose under substitution.

## What is not mechanised

| prerequisite from §8 of the problem statement | state |
| --- | --- |
| reduction and conversion on the full syntax | not defined |
| general weakening for indexed families | open (fragment and `Eq` only) |
| general substitution and context morphisms | fragment only |
| subject reduction | only the beta step on the fragment |
| progress | open |
| strong normalisation and confluence | open |
| logical relation or contextual equivalence | not defined |
| supercompiler translation and transport proof | interface and beta instance only |

The paper plan explains why the last row is not a missing lemma: the semantic
regime needs either univalence or a logical relation, and neither is derivable
from the metatheory that is present.
