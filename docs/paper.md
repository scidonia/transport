# Paper plan: transport for supercompilation

Working title: **Transport for Supercompilation: Type Preservation as a
Displayed Functor**

The thesis is that a type-preserving supercompiler is not justified by subject
reduction.  It is justified by a transport operation along the supercompiler's
translation of contexts and types.  In homotopy type theory that operation is
transport along a path in a universe; in plain Martin-Löf type theory it is
either definitional equality, the identity eliminator, or a clause of a logical
relation.  The paper separates those three cases and shows what a supercompiler
must supply in each.

## Abstract

Supercompilation replaces a program by a residual program, not by a reduct.
The residual program is produced by driving, specialization, folding, and
generalization, and it need not have the source type.  The standard
type-preservation argument for an operational semantics therefore does not
apply.  We formulate the correctness condition as a transport theorem: for
every typed source term there are relations between source and residual
contexts and types, and a term-level transport that reads the residual program
back at the source type.  We identify three regimes: definitional equality,
propositional equality, and semantic equivalence.  The first is `refl`; the
second is the identity eliminator; the third requires a logical relation, or
univalence if the type theory has it.  We give a category-with-families account
in which a supercompiler is a displayed functor and transport is its Cartesian
lift, and we mechanise the definitional and fragment cases in Lean 4.

## 1. Introduction

A supercompiler observes how a program behaves under symbolic driving, builds a
residual program from the resulting configurations, and folds repeated
configurations into recursive calls.  The literature is mostly about
termination and efficiency.  Types enter in two places: the source program is
typed, and the residual program is run.

The naive type-preservation statement

$$
\Gamma \vdash t : A \quad\Longrightarrow\quad \Gamma \vdash sc(t) : A
$$

is false.  The supercompiler may specialize an index, reduce under a binder
that the source reduction relation cannot reach, fold a term at a different
type, or generalize a configuration.  Even when `sc(t)` is semantically the
same program, its type can differ from `A`.

Contributions:

1. A precise transport theorem for a typed supercompiler on an indexed
   Martin-Löf type theory, with the context and type translations as explicit
   data (`Transport/Spec.lean`).
2. A separation of the three equality regimes and the proof obligation each
   one induces.
3. A fragment in which the metatheory is complete: renaming, substitution,
   and beta contraction preserve typing, and the transport theorem is
   instantiated at a non-identity term translation (`Transport.Mltt.Fragment`,
   `Transport.Mltt.Beta`).
4. A displayed-functor reading of the same theorem, connecting the syntactic
   obligation to the homotopy interpretation: transport is the action on a
   path, and the missing principle in plain MLTT is univalence.

## 2. The problem

### 2.1 Supercompilation in one paragraph

A supercompiler drives a term with symbolic inputs, producing a tree of
configurations.  It then performs a roll-up: a configuration that is an
instance of an earlier one becomes a call to a residual function, and the
residual program is the folded tree.  The residual program is not a reduct of
the source term.  Subject reduction talks about `t →* t'`; supercompilation
talks about `t ↝ t_res`.

### 2.2 The naive statement fails

For an indexed type `Vec A n`, specialization can replace an index `n` by a
constructor form.  The residual term then inhabits `Vec A (suc k)` while the
source term inhabits `Vec A n`; the two types are propositionally equal only
if `n = suc k` is derivable.  Folding can replace a subterm by a call to a
residual function whose type is a generalization of the subterm's type.  A
type-preservation lemma for `sc` must therefore mention a relation between the
source and residual types, not just the terms.

### 2.3 Three regimes

| regime | witness | transport |
| --- | --- | --- |
| definitional | `A ≡ A'` | `refl`, the term is already at `A` |
| propositional | `p : Id Ty A A'` | the identity eliminator `J` |
| semantic | `A ~ A'` only | no internal term; a logical relation or a model |

Plain MLTT does not make every equivalence an identity.  Univalence does.  The
paper's central observation is that the regime is a property of the type theory,
not of the supercompiler: the same residual program needs `J` in one theory and
a logical relation in another.

## 3. Formal setting

### 3.1 Syntax and typing

The object theory has `Tm`, `Ctx`, `Env`, and `HasType`.  The type formers are
`sort`, `pi`, and indexed families with parameters, indices, and constructor
signatures.  `roll` is the constructor former; `case` is the index-refining
eliminator, with a motive that binds the indices and the scrutinee.  The typing
rules for `ind`, `roll`, and `case` compute their result types with `substMany`
and `substParams`.

The formalisation is deliberately small: Lean core and Std only, no mathlib,
and no stored reference proof of the transport theorem.

### 3.2 The fragment

The general `case`/`roll` rules quantify over a signature and substitute its
types; the signature representation does not record that a parameter type's
free variables are within the parameter telescope.  General weakening is
therefore blocked at the signature boundary, not at the term level.  The
fragment `Simple` removes `fix`, `ind`, `roll`, and `case`, and keeps `var`,
`sort`, `pi`, `lam`, and `app`.  On it, renaming and substitution are complete.

### 3.3 Translation data

A translation is

$$
scCtx : Ctx \to Ctx,\qquad scTy : Ty \to Ty,\qquad scTm : Tm \to Tm.
$$

A supercompiler is a translation plus relations `ctxRel` and `tyRel` and the
typing direction

$$
\Gamma \vdash t : A \;\Longrightarrow\; scCtx\,\Gamma \vdash scTm\,t : scTy\,A.
$$

## 4. The transport theorem

A `TransportData` is a relation on contexts, a relation on types, an operation

$$
transport : ctxRel\,\Gamma\,\Gamma' \to tyRel\,A\,A' \to Tm \to Tm,
$$

and its soundness:

$$
\frac{ctxRel\,\Gamma\,\Gamma' \qquad tyRel\,A\,A' \qquad
\Gamma' \vdash t : A'}{\Gamma \vdash transport\,t : A}.
$$

Given `ctxRel Γ (scCtx Γ)` and `tyRel A (scTy A)`, the theorem is

$$
\Gamma \vdash t : A \;\Longrightarrow\;
\Gamma \vdash transport\,(scTm\,t) : A.
$$

The relations are `Type`-valued, so a certificate is data: two transformations
with the same endpoints can carry different substitutions, folds, or migration
maps.  Only soundness is a proposition.  The content is in the data, not in the
composition.  The paper should say this plainly: the theorem is a schema, and
the research question is which instance of the schema a given supercompiler
admits.

### 4.1 Coherence

A transport operation is expected to satisfy

$$
transport_{refl}\,t = t,\qquad
transport_{p \cdot q}\,t = transport_q\,(transport_p\,t),
$$

context-extension and type-former congruence, and substitution stability

$$
scTm\,(t[\sigma]) \;\approx\; (scTm\,t)[sc\sigma].
$$

Without substitution stability the theorem does not compose across contexts
and cannot justify replacing a subterm inside a larger program.  This is the
most likely place for a supercompiler to fail: it can be correct on closed
terms and wrong under substitution.

### 4.2 What the mechanisation covers

`Transport/Spec.lean` states the theorem and the identity instance.
`Transport/Mltt/Beta.lean` provides a non-identity `scTm` (outermost beta
contraction) and proves the typing direction on the fragment.  The composition
is `Transport.BetaInstance.transport`.

The mechanisation does **not** prove substitution stability for a general
supercompiler; it proves the substitution lemma that a beta step needs.

Stage 2's first instance is `Transport/Certificate.lean`: a first-order list
expression language, the reverse-accumulator generalisation, a syntactic
certificate checker, and a soundness theorem over all closing substitutions.
It checks one certificate, not a general process graph.

A separate component baseline is mechanised.  `Transport/Orbit.lean` defines
orbit connectivity for an arbitrary endofunction, proves it is an equivalence,
and instantiates it at the outermost beta function.  The two typed fixed points
`λx. (λy. y) x` and `λx. x` are disconnected in the initial calculus and
connected once contraction under a binder is admitted.  This needs no
normalisation theorem.

## 5. The logical-functor account

A category with families has a category of contexts, a presheaf of types, a
presheaf of terms over types, context extension, and type formers.  A
supercompiler that changes types is a **displayed functor**: the residual type
lives over the translated context.

- A context morphism is a substitution.
- A type is a family over contexts.
- A term is a section.
- The supercompiler is a functor on the base and a displayed functor on the
  families.
- Transport is the Cartesian lift of the displayed morphism.

The coherence laws of §4.1 are the functor laws.  The syntactic theorem is the
type-theoretic shadow of this structure.  This is stronger than a list of
preservation lemmas; in particular, it rules out a supercompiler that is
correct on closed terms but not under substitution.

The paper should present the CwF account as the organizing principle and the
Lean fragment as evidence that the syntactic instance is the expected one.

## 6. The homotopy reading

### 6.1 Paths and transport

In Martin-Löf type theory, the identity type `Id A x y` is the type of paths.
For a type family `P : A → Type`, identity elimination gives

$$
transport^P : Id\,A\,x\,y \to P\,x \to P\,y.
$$

The computation rule is `transport refl = id`, and transport composes
contravariantly.

### 6.2 The supercompiler's type translation as a path

The residual type is `scTy A`.  If the type theory has a universe `U` and a
path `p : scTy A = A` in `U`, then transport along `p` is exactly the operation
that reads the residual term back at the source type.  In the formalised object
theory, `Ty` is syntactic (`Tm`) and the path is a metatheoretic equality; the
Lean development uses `Eq.rec`.  The paper should be explicit about this
distinction rather than pretending the object theory internalises it.

### 6.3 Univalence

Univalence is

$$
(A \simeq B) \simeq (A = B).
$$

With `ua`, an equivalence between `scTy A` and `A` becomes a path, and transport
exists internally.  Without it, an equivalence is not an identity, and the
semantic regime has no internal transport term.  This is the precise sense in
which univalence is the missing principle for the third regime.

Lean's `Eq` is proof-irrelevant, so univalence cannot simply be added as an
axiom there: `Transport/UnivalenceObstruction.lean` proves that the round-trip
law forces the identity self-equivalence of `Bool` to equal negation.  The
paper's HoTT experiment uses Cubical Agda (`cubical/`), a theory designed for
HoTT with computational univalence and higher inductive types.  Binary vector
packing is checked, including `uaβ`/`~uaβ` computation, the three-vector
dependent-path coherence, and the 2-path between the two composite packing
paths.  Lean 4 HoTT
libraries were surveyed: Ground Zero is a synthetic library on an older Lean,
HoTTLean formalises the meta-theory, and Kubus is a separate verified cubical
proof assistant.  Kubus mechanises a cubical-sets model and canonicity; the
survey is in `docs/lean-hott-survey.md`.  The obstruction above is specific to
Lean's proof-irrelevant `Eq`, not to HoTT.

The displayed-functor picture makes the same point structurally: the displayed
category over `Ctx` can be discrete, a groupoid, or univalent.  The
supercompiler's correctness theorem changes with that choice.

### 6.4 What is not claimed

The paper does not claim that supercompilation is univalent, or that every
supercompiler's type translation is a path.  The claim is conditional: *if* the
translation is a path (definitional, propositional, or univalent), transport
exists; *if* it is only an equivalence, the theorem is semantic.

## 7. Mechanisation

| result | Lean name | status |
| --- | --- | --- |
| `Eq` `J` typing | `J_has_type_proof` | ported, proved |
| `Eq` weakening | `hasType_weaken_proof` | ported, proved |
| renaming/substitution algebra | `Subst.*` | proved |
| fragment renaming | `hasType_rename_simple` | proved |
| fragment substitution | `hasType_subst_simple`, `hasType_subst0_simple` | proved |
| beta preservation | `beta_preserves_hasType` | proved |
| transport schema | `transport_theorem` | proved |
| beta transport instance | `Transport.BetaInstance.transport` | proved |
| orbit connectivity | `Transport.Orbit.orbitConnected_equivalence` | proved |
| beta fixed-point separation | `Transport.Orbit.BetaInstance.typed_fixed_points_disconnected` | proved |
| beta fixed-point connection | `Transport.Orbit.BetaInstance.typed_fixed_points_connected_after_binder` | proved |
| reverse certificate checker | `Transport.Certificate.revCert_check` | proved |
| reverse certificate soundness | `Transport.Certificate.revCert_sound` | proved |
| reverse derivation soundness | `Transport.Derivation.Reverse.derivation_residual` | proved |
| finite-index migration | `Transport.IndexMigration.migrateIndex_val` | proved |
| zigzag compression | `Transport.CommonAncestor.zigzag_compress` | proved |
| successor common ancestors | `Transport.CommonAncestor.succ_zigzag_compress` | proved |
| fork zigzag counterexample | `Transport.CommonAncestor.Fork.fork_zigzag_not_compressible` | proved |
| zigzag vs forward reachability | `Transport.CommonAncestor.Fork.fork_zigzag_not_forward` | proved |
| quadratic reverse cost | `Transport.Cost.two_mul_reverseCost` | proved |
| linear accumulator cost | `Transport.Cost.revAccCost_eq_length` | proved |
| quadratic strict queue | `Transport.QueueCost.two_mul_strictEnqueueTotal` | proved |
| linear two-list queue | `Transport.QueueCost.two_list_linear` | proved |
| univalence obstruction over `Eq` | `Transport.Obstruction.no_univalence_with_proof_irrelevant_eq` | proved |
| reused Cubical Agda univalence | `cubical/Univalence.agda` | checked |
| vector packing | `cubical/Packing.agda` | checked |
| packing-route 2-path | `cubical/Coherence.agda` (`two-path`) | checked |
| three-vector coherence | `cubical/Packing.agda` (`three-vector-coherence`) | checked |

Trust: the main 4.35 core has no `sorry`, no `admit`, no `native_decide`, and
no new `axiom`; `#print axioms` reports `propext` and `Quot.sound`.

The paper should include the Lean statements verbatim in an appendix and state
the fragment boundary honestly.  The semantic case remains a paper-level
theorem and a formalisation target, not a mechanised result.

## 8. Discussion

### 8.1 Subject reduction is the wrong theorem

Subject reduction is about the source reduction relation.  A supercompiler's
residual program is not reached by that relation, so subject reduction neither
implies nor is implied by the transport theorem.  The right statement is
relational: the residual program is related to the source program at a
translated type, and the relation is stable under substitution.

### 8.2 Folding and generalization

Folding introduces a residual function; its type is a generalization of the
folded term's type.  This is where `tyRel` is not equality even in a univalent
theory: the residual function's type may be a pi-type over the generalized
arguments, and the fold is an application of that function.  A full treatment
needs the logical relation at function type, not just at base types.

### 8.3 Driving under binders

Driving can reduce an index under a binder where the source reduction relation
cannot.  The transport theorem is insensitive to *how* the residual type was
produced; it only asks for the relation and the typing direction.  This is a
feature: the same theorem covers driving, specialization, and fold.

### 8.4 The signature gap

The current indexed signature representation does not record the free-variable
bound of a parameter type.  General weakening needs that invariant.  The paper
should present the gap as a design lesson: a metatheory for an indexed syntax
must carry the telescope invariant, or the substitution lemmas are false as
stated.

## 9. Related work

- Supercompilation: Turchin; Sørensen, Glück, and Jones; Glück and Sørensen.
- Partial evaluation: Jones, Gomard, and Sestoft.
- Categories with families: Dybjer; Hofmann.
- Displayed categories and fibrations: Ahrens and Lumsdaine; Shulman.
- Homotopy type theory: the HoTT book; Awodey and Warren; Kapulkin and
  Lumsdaine; Shulman on univalent universes.
- Lean 4 implementations evaluated but not used as the active layer:
  Ground Zero (synthetic HoTT library, `ua`/`uaβ`); HoTTLean (groupoid model
  and SynthLean); Kubus (verified cubical proof assistant with univalence and
  canonicity in its object language).
- Normalisation and logical relations for dependent types: Abel; Coquand;
  Sterling and Angiuli.
- Type-preserving compilation and typed intermediate languages, as the
  engineering counterpart of the transport obligation.

## 10. Conclusion

Supercompilation changes the program and may change its type.  Correctness is
therefore a transport theorem, not a subject-reduction lemma.  The three
equality regimes determine whether that theorem is `refl`, `J`, or a logical
relation.  The displayed-functor account explains why, and the Lean fragment
shows the definitional case end to end.  The remaining work is the semantic
case: a logical relation stable under substitution, and a univalent model in
which equivalences become transports.

## Appendix: Lean statements

```lean
theorem transport_theorem (sc : Supercompiler) (td : TransportData)
    (hctx : ∀ Γ, td.ctxRel Γ (sc.translation.scCtx Γ))
    (hty : ∀ A, td.tyRel A (sc.translation.scTy A))
    (htm : ∀ {env Γ t A}, HasType env Γ t A →
      HasType env (sc.translation.scCtx Γ)
        (sc.translation.scTm t) (sc.translation.scTy A)) :
    ∀ {env Γ t A}, HasType env Γ t A →
      HasType env Γ
        (td.transport (hctx Γ) (hty A) (sc.translation.scTm t)) A

theorem beta_preserves_hasType {env Γ t A}
    (ht : HasType env Γ t A) (hs : Simple t) :
    HasType env Γ (beta t) A

theorem Transport.BetaInstance.transport {env Γ t A}
    (h : HasType env Γ t A) (hs : Mltt.Subst.Simple t) :
    HasType env Γ (beta t) A
```
