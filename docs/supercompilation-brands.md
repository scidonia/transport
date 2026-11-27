# Supercompilation brands and the certificate interface

The current development is one instantiation: first-order reverse, an
accumulator schema, a fold, and a residual label.  The action/certificate
architecture is not specific to that instantiation.

A supercompiler brand fixes:

```text
Config        the process states
Step          the process transition relation
Obs           the observation/result relation
Gen           the generalisation relation (schema + instantiation)
Fold          the label/fold relation
LR            the target equivalence at the type
Whistle       the search/termination policy
Strategy      positive/negative/multi-result, if any
```

The proof-carrying actions stay the same:

```text
drive(c,c')          : a step certificate
generalise(s,g)      : a GenCert
fold(s,label)        : a FoldCert
residualise(c)       : an observation certificate
cert(s,r)            : a leaf certificate
```

A transform is a tree of these actions.  The brand chooses the language, the
search, and the certificates' relations; it does not choose whether certificates
are checked.

## 1. What changes per brand

| brand | process graph | generalisation | fold | equivalence | change to the certificate layer |
| --- | --- | --- | --- | --- | --- |
| Turchin first-order | first-order process tree | anti-unification / MSG | letrec/label | contextual or bisimulation | first-order `SBisim`; current form |
| HOSC (higher-order) | higher-order process trees, closures, letrec | higher-order patterns / MSG | higher-order letrec label | applicative/Kripke bisimulation or LR at function types | function-space clauses; higher-order `GenCert`; guarded higher-order `FoldCert` |
| supercompilation by evaluation | evaluation-driven tree | evaluation/generalisation | letrec/normalisation | observational equivalence | `drive` carries an evaluation/normalisation certificate |
| distillation | process tree with different driving/residualisation | distillation generalisation | letrec | contextual/bisimulation | different `drive`/`residualise` actions |
| positive supercompilation | finite/whistled tree | as chosen | as chosen | as chosen | a **stop/whistle** action with a certificate |
| negative supercompilation | tree with rejected folds | as chosen | rejected/negative | as chosen | a **negative** action carrying a counterexample/refutation |
| multi-result | forest/relation of residuals | as chosen | as chosen | as chosen | a **forest**; correctness is the conjunction of all leaf certificates |
| partial evaluation | no fold/generalisation | none | none | simulation/equivalence | only `drive`/`residualise`; a restricted action calculus |

## 2. HOSC specifically

Higher-order/higher-level supercompilation changes four things:

1. **Language.**  Configurations contain higher-order terms/closures,
   application, binders, and `letrec`.  The step relation is higher-order
   evaluation, not a first-order list step.
2. **Process graph.**  Driving produces higher-order process trees; the nodes
   may be closures or open terms.  Observations are values/normal forms at
   higher types, not just list results.
3. **Generalisation.**  The schema is higher-order: it may abstract over
   functions, contexts, or patterns.  The algorithmic form is a higher-order
   anti-unification/MSG; the oracular form returns the same `GenCert` with a
   proof.
4. **Fold and equivalence.**  The label is a higher-order recursive definition.
   The bisimulation has an applicative/Kripke function clause; the typed
   relation has a `Pi` clause and is stable under application/contexts.  A
   `FoldCert` needs the higher-order unfolding, guardedness, and a bisimulation
   at the function type.

The whistle/generalisation search is a **selection policy**; it can be
algorithmic (homeomorphic embedding, depth, size) or oracular.  It is not a
proof rule: the accepted actions still carry checked certificates.  A rejected
fold is a negative certificate, not an unchecked optimisation.

## 3. What remains invariant

- Actions are proof-carrying.
- `GenCert` contains a schema, an instantiation, and a relation proof.
- `FoldCert` contains the unfolding, the relation/bisimulation, and guardedness.
- A transform is a derivation tree/forest; the final certificate is composed.
- The oracle is a proof producer; the kernel checks.
- The final theorem is a typed relation, then transport/contextual equivalence.

## 4. What the current code fixes

The action layer is now parameterised:

- `Transport/Action.lean` defines `Process` (`Config`, `Step`, `Obs`),
  step-indexed `Bisim`, `FoldCert`, and `Derivation` independently of the reverse
  worker;
- `Transport/ActionReverse.lean` instantiates the reverse source/residual
  processes and proves `reverseDerivation_sound`.

Generic generalisation is also in place: `Action.GenCert` is parameterised by a
process pair and a parameter type, and `Derivation.generalise` carries it.
`ActionReverse.reverseGenCert`/`reverseGeneralised` are the regression instance.

Still specific to reverse/`Certified`:

- the list base relation `ListRel`;
- the `RDerivation` action tree built on the specific reverse types.

To support other brands, continue with:

1. a typed `LR`/bisimulation for the target types, parameterised over the process;
2. a selection/whistle/oracle interface;
3. a result shape: single term, forest, or positive/negative set;
4. higher-order `Pi`/application clauses and higher-order generalisation.

The reverse instance remains a regression test: the action tree, the
generalisation certificate, the fold certificate, and the final typed relation
must still compose.

## 5. Order of work

1. Parameterise the action calculus over `Config`, `Step`, `Obs`, and the
   certificate relations.
2. Add a second first-order instance with a different generalisation/fold policy
   to validate parameterisation.
3. Add a higher-order fragment: lambda/application/letrec, an applicative or
   Kripke step-indexed bisimulation, and a function-space `LR`.
4. Add a multi-result or positive/negative variant at the action level.
5. Move to the dependent `Pi`/identity/inductive-family LR and transport.

The certificate architecture should not need to change for those brands; the
instantiations and the selection policy should.
