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

The transport theorem is stated as data, not assumed: a `Supercompiler` supplies
the typing direction `HasType Γ t A → HasType (scCtx Γ) (scTm t) (scTy A)`, a
`TransportData` supplies the operation that reads a residual term back at the
source context and type together with its soundness, and
`Transport.transport_theorem` composes them.

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
Transport/Spec.lean            translation, transport data, the theorem
docs/                          problem statement, paper plan, formalisation map
```

## License

Apache License 2.0.  See [LICENSE](LICENSE).
