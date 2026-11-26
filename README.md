# transport

Type-preserving supercompilation for Martin-Löf type theory, and the transport
theorem that a residual program needs.

A supercompiler does not return a reduct of its input.  It returns a residual
program in a translated context and at a translated type.  The question this
repository formalises is what it means for that residual program to have the
source type, and what has to be proved for the replacement to be sound.

The problem statement is [docs/transport-mltt.md](docs/transport-mltt.md).  The
paper plan, which relates the syntactic transport theorem to the homotopy
interpretation, is [docs/paper.md](docs/paper.md).  The Lean development is
summarised in [docs/formalization.md](docs/formalization.md).

## Build

The toolchain comes from the flake; nothing needs to be activated.

```bash
nix develop -c lake build
```

No Lean dependencies.  The development uses Lean core and Std only.

The HoTT model reuses the existing Cubical Agda library rather than
axiomatising univalence over Lean's `Eq`:

```bash
nix develop .#cubical -c bash -c 'cd cubical && agda --cubical --guardedness Univalence.agda'
```

## What is proved

| result | Lean name |
| --- | --- |
| `Eq` `J` eliminator typechecks | `Transport.Mltt.J_has_type_proof` |
| weakening for the `Eq` family | `Transport.Mltt.Weaken.hasType_weaken_proof` |
| renaming and substitution algebra | `Transport.Mltt.Subst.*` |
| substitution preserves typing on the function fragment | `Transport.Mltt.Fragment.hasType_subst_simple` |
| beta contraction preserves typing on the fragment | `Transport.Mltt.Beta.beta_preserves_hasType` |
| transport theorem schema | `Transport.transport_theorem` |
| definitional transport, instantiated at beta | `Transport.BetaInstance.transport` |
| orbit connectivity is an equivalence | `Transport.Orbit.orbitConnected_equivalence` |
| typed beta fixed points, separated then joined | `Transport.Orbit.BetaInstance.typed_fixed_points_disconnected`, `typed_fixed_points_connected_after_binder` |
| first-order reverse certificate checker | `Transport.Certificate.revCert_check`, `revCert_sound` |
| univalence cannot be added over Lean's `Eq` | `Transport.Obstruction.no_univalence_with_proof_irrelevant_eq` |

The stage-2 certificate is in `Transport/Certificate.lean`: the source and
generalised expressions are data, the checker decides their syntactic shape,
and `revCert_sound` proves that the residual accumulator worker returns the
source value for every closing substitution.  The fold decrease is explicit.
This is one certificate, not yet a general process graph.

The first component result is also in place: `Transport/Orbit.lean` proves that
orbit connectivity is an equivalence for any endofunction, that
`λx. (λy. y) x` and `λx. x` are typed fixed points of the outermost beta
function, that they lie in different components, and that adding contraction
under a binder connects them.  This does not assume normalisation.

The transport theorem is stated as data, not assumed: a `Supercompiler` supplies
the typing direction `HasType Γ t A → HasType (scCtx Γ) (scTm t) (scTy A)`, a
`TransportData` supplies the operation that reads a residual term back at the
source context and type together with its soundness, and
`Transport.transport_theorem` composes them.

## Univalence

Lean's identity type is a proposition, so any two proofs of the same equality
are equal.  `Transport/UnivalenceObstruction.lean` proves that a univalence map
`ua : (A ≃ B) → (A = B)` together with the round-trip law forces the identity
self-equivalence of `Bool` to equal negation.  Univalence is therefore not a
missing axiom that can simply be added over Lean's `Eq`.

The faithful model is `cubical/Univalence.agda`, which reuses the existing
Cubical Agda library: `ua`, its computation rule `uaβ`, and `uaIdEquiv`, with a
concrete transport through the univalence path of Boolean negation.

The two equalities are deliberately separate.  Lean's `Eq` is the equality of
the object theory and the metatheory; the univalent layer uses Cubical Agda's
path type `_≡_`.  The obstruction applies only to the former.

`rzrn/ground_zero` is an existing Lean 4 HoTT library with `ua`/`uaβ`, but it
pins Lean 4.28; its `Id` is `Type`-valued, while Lean 4.35's relation classes
are `Prop`-valued, so it needs a library migration rather than a version bump.

## What is open

The semantic regime is not mechanised.  The current formalisation has:

- no reduction or conversion relation on the full indexed syntax;
- no general weakening or substitution for the inductive families (the `Eq`
  case is proved, the function fragment is proved, the general `substMany`
  side conditions are not);
- no subject reduction, progress, strong normalisation, or confluence;
- no logical relation or contextual equivalence;
- no univalence, so an equivalence between types is not a transport path.

The paper plan states why those gaps are the content of the semantic case
rather than a missing lemma.

## Provenance

The MLTT syntax and typing rules, the `J` typing proof, and the `Eq` weakening
proof are ported from `scidonia/proof-approach` at commit `4e1ba39`.  Their
namespaces are changed from `Problems.Hard.*` to `Transport.Mltt.*` and the
doc comments are adapted to this repository; the proof bodies are unchanged.

## Layout

```
Transport/Mltt/Core.lean       syntax, contexts, indexed typing
Transport/Mltt/J.lean          Eq/J typing proof
Transport/Mltt/Weaken.lean     Eq weakening proof and renaming algebra
Transport/Mltt/Subst.lean      substitution algebra and the fragment predicate
Transport/Mltt/Fragment.lean   renaming and substitution on the fragment
Transport/Mltt/Beta.lean       beta contraction and its typing theorem
Transport/Orbit.lean           orbit connectivity and the beta fixed points
Transport/Certificate.lean     first-order reverse certificate and checker
Transport/UnivalenceObstruction.lean  no univalence over proof-irrelevant Eq
Transport/Spec.lean            translation, transport data, the theorem
cubical/Univalence.agda        reused Cubical Agda ua/uaβ test
docs/                          problem statement, paper plan, formalisation map
```

## License

Apache License 2.0.  See [LICENSE](LICENSE).
