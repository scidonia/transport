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
summarised in [docs/formalization.md](docs/formalization.md).  The
metatheory needed for a full dependent supercompiler is staged in
[docs/dependent-basis.md](docs/dependent-basis.md).  The full
characterisation programme is [docs/mltt-programme.md](docs/mltt-programme.md).

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
| dependent case for constructor telescopes (separate relation) | `Transport.Mltt.Dependent.HasTypeDep.caseDep` |
| dependent case with a constructor parameter | `Transport.Mltt.Dependent.unit_caseDep` |
| result-index substitution in dependent constructors | `Transport.Mltt.Dependent.HasTypeDep.rollDep` |
| dependent case with a dependent motive | `Transport.Mltt.Dependent.Motive.unit_caseDep_motive` |
| labelled reverse fold with a step-indexed bisimulation | `Transport.Certified.FoldCert`, `reverseFold`, `residual_sound` |
| independent residual label and source/residual bisimulation | `Transport.Certified.ResidualFoldCert`, `R_bisim`, `residual_run` |
| accumulator generalisation certificate | `Transport.Certified.GenCert`, `algorithmicGen`, `genCert_instance` |
| certified reverse supercompiler loop | `Transport.Certified.RDerivation`, `reverseDerivation`, `reverseDerivation_sound` |
| composable transform actions | `Transport.Certified.RDerivation.cert`, `generalise`, `fold`, `halt`; `reverseGeneralised` |
| base heterogeneous list logical relation | `Transport.Certified.ListRel`, `reverse_residual_LR` |
| full-argument signature invariant | `Transport.Mltt.Conventions.WellFormedSigFull` |
| positivity gate for the full-argument signatures | `Transport.Mltt.Conventions.vecDep_gate`, `finDep_gate`, `eqDep_gate`, `natDep_gate` |
| `Eq`/`Nat`/`Vec`/`Fin` signatures in the full-argument convention | `Transport.Mltt.Conventions.eqDep_wellFormed`, `natDep_wellFormed`, `vecDep_wellFormed`, `finDep_wellFormed` |
| well-scoped invariant; identity renaming below the depth | `Transport.Mltt.Scoped.rename_upRenN_of_wellScoped` |
| `Eq` signature invariant and scoped substitution commutation | `Transport.Mltt.Scoped.eq_sig_wellFormed`, `substMany_rename_of_wellScoped` |
| weakening for the `Eq` family | `Transport.Mltt.Weaken.hasType_weaken_proof` |
| renaming and substitution algebra | `Transport.Mltt.Subst.*` |
| substitution preserves typing on the function fragment | `Transport.Mltt.Fragment.hasType_subst_simple` |
| beta contraction preserves typing on the fragment | `Transport.Mltt.Beta.beta_preserves_hasType` |
| transport theorem schema | `Transport.transport_theorem` |
| definitional transport, instantiated at beta | `Transport.BetaInstance.transport` |
| orbit connectivity is an equivalence | `Transport.Orbit.orbitConnected_equivalence` |
| typed beta fixed points, separated then joined | `Transport.Orbit.BetaInstance.typed_fixed_points_disconnected`, `typed_fixed_points_connected_after_binder` |
| first-order reverse certificate checker | `Transport.Certificate.revCert_check`, `revCert_sound` |
| reverse derivation soundness | `Transport.Derivation.Reverse.derivation_residual` |
| finite-index migration | `Transport.IndexMigration.migrateIndex_val`, `migrate_trans`, `migrateIndex_map` |
| zigzag compression | `Transport.CommonAncestor.zigzag_compress` |
| successor common ancestors | `Transport.CommonAncestor.succ_zigzag_compress` |
| fork zigzag with no common ancestor | `Transport.CommonAncestor.Fork.fork_zigzag_not_compressible` |
| zigzag vs forward reachability | `Transport.CommonAncestor.Fork.fork_zigzag_not_forward` |
| quadratic naïve-reverse cost | `Transport.Cost.two_mul_reverseCost` |
| linear accumulator cost | `Transport.Cost.revAccCost_eq_length` |
| accumulator cheaper | `Transport.Cost.revAccCost_le_reverseCost` |
| strict queue quadratic cost | `Transport.QueueCost.two_mul_strictEnqueueTotal` |
| two-list queue linear cost | `Transport.QueueCost.two_list_linear` |
| two-list queue beats strict | `Transport.QueueCost.two_list_beats_strict` |
| univalence cannot be added over Lean's `Eq` | `Transport.Obstruction.no_univalence_with_proof_irrelevant_eq` |

The stage-3 index migration is in `Transport/IndexMigration.lean`: an index of
`xs ++ ys` is migrated to the residual index `xs.length + ys.length` by the
identity eliminator, with value preservation, composition, successor
coherence, and stability under mapping the element type.

The stage-2 certificate is in two layers.  `Transport/Certificate.lean` checks
the source and generalised expressions and proves the accumulator worker
returns the source value for every closing substitution.  `Transport/Derivation.lean`
adds the process graph: configurations, drive/fold/residualise edges, and a
derivation whose type is the certificate.  Its soundness theorem quantifies
over every input and accumulator, and the fold decrease is explicit.  This is
one worker, not yet a general process-graph engine.

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

The univalent layer uses **Cubical Agda**, a type theory designed for HoTT with
computational univalence and higher inductive types.  `cubical/Univalence.agda`
reuses `ua`, `uaβ`, and `uaIdEquiv`, with a concrete transport through the
univalence path of Boolean negation.

`cubical/Packing.agda` adds the binary vector packing: split/append are
inverses, `transport (ua packEquiv)` computes to append, the backward
transport computes to split, and the three-vector routes agree by the library's
append associativity.  Cubical Agda warns that the round-trip proofs use
indexed pattern matching and do not compute under transports; the `uaβ` and
`~uaβ` computation laws themselves are checked.

`cubical/Coherence.agda` proves the two composite packing routes agree: the
forward functions are related by append associativity, `equivPathP` lifts that
to a dependent path of equivalences, and univalence yields a 2-path between the
two composite `ua` paths.

Lean 4 HoTT libraries were surveyed and are not part of the active build:
Ground Zero is a synthetic library pinned to an older Lean; HoTTLean
formalises the meta-theory; Kubus is a separate verified cubical proof
assistant.  The survey, sources, and decision are in
[docs/lean-hott-survey.md](docs/lean-hott-survey.md).  Kubus is the trust
anchor; Ground Zero is not a consistency proof.

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
Transport/Mltt/Scoped.lean     well-scoped terms and the proposed signature invariant
Transport/Mltt/Subst.lean      substitution algebra and the fragment predicate
Transport/Mltt/Fragment.lean   renaming and substitution on the fragment
Transport/Mltt/Beta.lean       beta contraction and its typing theorem
Transport/Mltt/Dependent.lean  dependent case with constructor branch telescopes
Transport/Mltt/DependentMotive.lean  dependent motive P scrut and branch p A
Transport/Certified.lean  labelled reverse fold and step-indexed bisimulation
Transport/Mltt/Conventions.lean  full-argument signatures and their telescope invariant
Transport/Orbit.lean           orbit connectivity and the beta fixed points
Transport/Certificate.lean     first-order reverse certificate and checker
Transport/Derivation.lean      drive/fold/residualise derivation and soundness
Transport/IndexMigration.lean  finite-index migration along length equations
Transport/CommonAncestor.lean  zigzag compression and the successor instance
Transport/Cost.lean            reversal cons-cell costs
Transport/QueueCost.lean       strict-list vs two-list queue costs
Transport/UnivalenceObstruction.lean  no univalence over proof-irrelevant Eq
Transport/Spec.lean            translation, transport data, the theorem
cubical/Univalence.agda        reused Cubical Agda ua/uaβ test
cubical/Packing.agda            vector packing, ua computation, three-vector coherence
cubical/Coherence.agda          the 2-path between the composite packing paths
docs/                          problem statement, paper plan, formalisation map
```

## License

Apache License 2.0.  See [LICENSE](LICENSE).
