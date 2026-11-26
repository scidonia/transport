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

## First-order certificate

`Transport/Certificate.lean` is the first stage-2 certificate.

- `LExp` is a first-order list expression language; `LExp.eval` interprets it
  under a closing environment.
- `genExpr` is `append (reverse (var 0)) (var 1)`, and `genEval_step` proves
  the fold equation `genEval (x :: xs) a = genEval xs (x :: a)`.
- `revAcc` is the residual accumulator worker; `revAcc_reverse` proves it
  returns the source value at the initial accumulator.
- `RevCert` stores the source, generalisation, fold parameter, accumulator
  parameter, and initial accumulator as data; `RevCert.check` decides the
  syntactic predicate.
- `revCert_sound` quantifies over every closing substitution (`∀ xs`) and
  proves the worker equals the source expression; `fold_decrease` records the
  structural decrease.

This checks one certificate.  A general process graph, drive branches, and
changed interfaces are not implemented.

## Derivation

`Transport/Derivation.lean` adds the process-graph layer for the same worker.

- `Config α` is `(xs, a)`; `denote` is `xs.reverse ++ a`.
- `Edge` has `driveNil`, `driveCons`, `fold`, and `residualise` constructors,
  with source and target configurations as indices.
- `Edge.sound` proves every edge preserves `denote`; `Edge.fold_decrease`
  proves the recursive input is a proper subterm.
- `Derivation` is a finite chain of edges; `Derivation.sound` composes the
  edge soundness theorems.
- `Reverse.derivation` builds the derivation for every input and accumulator;
  `Reverse.derivation_sound` and `Reverse.derivation_residual` state the
  worker's correctness.

The type indices are the certificate; Lean's kernel checks it.  This is still
one worker, not a general process-graph engine.

## Univalence

Lean's `Eq` is a proposition, so proofs of the same equality are equal.
`Transport/UnivalenceObstruction.lean` makes the consequence explicit:

```lean
theorem no_univalence_with_proof_irrelevant_eq
    (ua : ∀ {A B : Type}, Equiv A B → A = B)
    (ua_round : ∀ {A B : Type} (e : Equiv A B),
      Equiv.ofEq (ua e) = e) : False
```

The proof uses the identity and negation self-equivalences of `Bool`:
`ua_round boolNot` has type `Equiv.ofEq (ua boolNot) = boolNot`, and the left
side reduces to the identity equivalence because `ua boolNot` is a proof of
`Bool = Bool`.  So univalence is not an axiom one can add over Lean's `Eq`.

The Cubical Agda file `cubical/Univalence.agda` reuses the existing library:

- `ua-compute = uaβ`: transport along `ua e` computes to `equivFun e`;
- `not-transport = uaβ notEquiv true`: a concrete Boolean migration;
- `ua-id = uaIdEquiv`: the identity equivalence gives the identity path.

The development therefore keeps two equalities: Lean's `Eq` for `HasType` and
the transport theorem, and Cubical Agda's `_≡_` path type for the univalent
layer.  The obstruction is a statement about the first, not a claim that no
proof-relevant equality exists.

Build: `nix develop .#cubical -c bash -c 'cd cubical && agda --cubical --guardedness Univalence.agda'`.

Lean 4 HoTT libraries were surveyed and are not part of the active build.
Ground Zero is a synthetic Lean 4 library with a proof-relevant `Id` and a
large-elimination checker; it builds on Lean 4.27 and its `notTransport`
computation checks, but it is pinned to an older Lean and does not mechanise a
consistency model.  HoTTLean formalises the groupoid model and a proof mode on
Lean 4.25 with Mathlib/Poly.  Kubus is a separate verified cubical proof
assistant and is the trust anchor.  The survey and sources are in
[lean-hott-survey.md](lean-hott-survey.md).

## Vector packing

`cubical/Packing.agda` is stage 4.

- `splitAt m` splits `Vec A (m + n)` into `Vec A m × Vec A n`.
- `splitAt-++` and `pack-split` prove the two round trips.
- `packEquiv` is the induced equivalence and `packPath` is its `ua` path.
- `pack-transport` is `uaβ`: transport along the path computes to append.
- `unpack-transport` is `~uaβ`: the backward transport computes to split.
- `three-vector-coherence` is the library's `++-assoc`: the two packing routes
  agree as a dependent path over `+-assoc`.

Cubical Agda emits `UnsupportedIndexedMatch` warnings for `splitAt-++` and
`pack-split`: those proofs rely on injectivity of the length constructors and
do not compute under transports.  `splitAt`, `pack`, `uaβ`, and `~uaβ` are not
affected.  The warning is a limitation to state in the paper, not a failure.

## Finite-index migration

`Transport/IndexMigration.lean` is stage 3.

- `migrate h i` moves `i : Fin m` to `Fin n` along `h : m = n`; its value is
  unchanged.
- `migrate_val`, `migrate_refl`, `migrate_trans`, and `migrate_succ` give the
  computation and coherence laws.
- `SourceIndex xs ys` is `Fin (xs ++ ys).length`; `ResidualIndex xs ys` is
  `Fin (xs.length + ys.length)`.
- `migrateIndex` migrates along `List.length_append`; `migrateIndex_val`
  preserves the value; `migrateIndex_map` shows stability under mapping the
  element type.

This is the identity eliminator at `Fin`, the definitional/propositional
regime.  The univalent version is the Cubical Agda layer.

## Common ancestors

`Transport/CommonAncestor.lean` is stage 5's common-ancestor result.

- `Star R` is the forward reflexive-transitive closure.
- `Zigzag R` allows steps in either direction.
- `CommonAncestor R p q` is `∃ h, Star R h p ∧ Star R h q`.
- `CoConfluent R` says every two paths into a common descendant have a common
  ancestor (confluence of the reversed relation).
- `zigzag_compress` proves every zigzag compresses to a common-ancestor span.
- `Succ` is the successor calculus on `Nat`; `star_succ_iff` characterises its
  star, `succ_coconfluent` proves reverse confluence, and
  `succ_zigzag_compress` is the concrete instance.
- `ForkNode`/`ForkStep` is the fork `A → C ← B`.  `star_from_C`, `star_from_A`,
  and `star_from_B` characterise its paths; `no_commonAncestor_AB` proves the
  fork has no common ancestor; `fork_not_coconfluent` shows reverse confluence
  fails; `fork_zigzag_not_compressible` is the minimal zigzag that cannot be
  compressed.  This shows the hypothesis is necessary.  `fork_zigzag_not_forward`
  proves the same fork is a zigzag from `A` to `B` but has no forward path,
  so zigzag connectivity is strictly weaker than forward reachability.

## Reversal costs

`Transport/Cost.lean` is stage 5's cost model, counting allocated cons cells
only.

- `reverseCost` follows `reverse (x :: xs) = reverse xs ++ [x]`.
- `revAccCost` is one cons per element.
- `two_mul_reverseCost` proves `2 * reverseCost xs = xs.length * (xs.length + 1)`.
- `revAccCost_eq_length` proves the accumulator is linear.
- `revAccCost_le_reverseCost` proves it is never more expensive than the
  naïve source.

## Queue costs

`Transport/QueueCost.lean` compares two queue implementations at the
cons-cell count.

- `strictEnqueueTotal` is the total for `n` enqueues into a strict list;
  `two_mul_strictEnqueueTotal` proves it is quadratic.
- `twoListTotalCost` is `n` enqueues plus one refill of `n` elements;
  `two_list_linear` proves it is linear.
- `two_list_beats_strict` proves the two-list total is no worse from three
  elements.

This is a cost comparison for two implementations, not the general lower bound:
the claim that any linear solution must change the representation or machine
assumptions is a separate argument.

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
| univalence over Lean's `Eq` | impossible (obstruction) |
| univalence model, Cubical Agda | reused in `cubical/` |

The paper plan explains why the last row is not a missing lemma: the semantic
regime needs either univalence or a logical relation, and neither is derivable
from the metatheory that is present.
