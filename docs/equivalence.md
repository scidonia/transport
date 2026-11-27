# Equivalence for the supercompiler

The transport theorem says what it means for a residual program to have the
source type.  It does not, by itself, say that the residual program is
equivalent to the source program.  That is a second theorem, and it needs a
chosen sense of equivalence.

The current development does not yet prove that theorem.  It has:

- a transport-data schema and a definitional beta instance;
- beta preservation for the function fragment;
- graph connectivity of orbits;
- Cubical Agda type-level packing and `uaβ`.

None of these is contextual equivalence of source and residual programs.

## 1. Four notions

| notion | level | role |
| --- | --- | --- |
| definitional equality `t ≡β u` | object syntax | internal conversion; typing up to it |
| contextual equivalence `t ≡ctx u : A` | observation | external program equality, same type |
| heterogeneous contextual equivalence `t ≈_{A,A'} u` | observation | external equality at related types |
| logical equivalence `LR_{A,A'}(t,u)` | semantics | heterogeneous proof tool |
| type relation `A ~ A'` / `e : A ≃ A'` | semantics/HoTT | relates types, not terms |
| type equivalence `A ≃ B` / path | HoTT | transport of types, not of programs |

The supercompiler needs the first two and a bridge between them.  The fourth is
the type-level action used by transport; it is not the term-level correctness
claim.

## 2. Why definitional equality is not enough

Supercompilation does not return a reduct:

```text
t : A
sc(t) : A'
```

Even when `A'` is definitionally `A`, the residual term need not be
definitionally equal to the source: specialization, generalization, folding,
and a changed evaluation context are not `Step` transitions.  Definitional
equality is the internal conversion; a supercompiler's correctness is an
external observational statement about the residual program.

## 3. Contextual equivalence

For a closed type `A`, define `t ≡ctx u : A` by closing under contexts:

```text
for every context C[-] with C[t], C[u] : B closed,
  obs(C[t]) = obs(C[u])
```

where `obs` is the chosen observation: a normal form, a constructor, a
canonical value, or an evaluation result for the total fragment.

For open terms, close under substitutions.  For dependent types, the context
must be typed and the relation type-directed: `C[-]` is a typing context with a
hole at type `A`.

This is the **observational** or **CIU** (closed-instance-of-use) equivalence
at a single type.  It is the natural external equality when both programs have
the same type.

### Heterogeneous CIU

The supercompiler does not preserve the type syntactically:

```text
t : A
sc(t) : A'
```

so `t ≡ctx sc(t) : A` is not even well-typed.  The general relation is indexed
by a **type relation** `R : A ~ A'`:

```text
t ≈ctx_R u
```

with `t : A`, `u : A'`.  It is defined by closing under **related contexts**:
a context `C[-]` with a hole at `A` and a context `C'[-]` with a hole at `A'`,
where the two contexts are related by a context relation (for dependent types,
a substitution relation / context morphism).  Observation is then related at
the result type.

The same-type CIU is the special case `A = A'` and `R` the equality relation.
The transport form is the same-type special case after moving the residual term:

```text
transport e (sc(t)) ≡ctx t : A
```

where `e : A ≃ A'`.  This is the form the supercompiler correctness theorem
should state if it privileges the source type.

The heterogeneous form is the semantic primitive; the transported same-type
form is its specialization.  Neither replaces the other:

- the heterogeneous relation explains why a residual term at a different type
  may be equivalent to the source;
- the transported relation is the closed theorem at the source type.

## 4. Logical equivalence

The standard proof tool is a **Kripke logical relation** indexed by contexts
and types:

```text
LR_{Γ~Γ', A~A'}(t,u)
```

indexed by a context relation and a type relation.  The same-type relation is
the special case of the identity/equality relation on a context and type.

with:

- a relation at base/inductive types;
- a Kripke function-space clause for `Pi`;
- a path/equality clause for the identity type;
- stability under weakening and substitution;
- a fundamental theorem for typing: related terms at related contexts are
  related at the type;
- adequacy: `LR` implies contextual equivalence.

For dependent types the relation must be **type-directed** and respect
conversion; a single untyped relation is not enough.  This is the semantic
bridge the programme has been missing.

## 5. Bisimulation and Howe

An **applicative bisimulation** relates terms by observing their behaviour
under application and evaluation.  **Howe's method** closes a candidate
bisimulation under contexts and proves the closure is a congruence; with CIU,
this yields contextual equivalence.  For the lazy untyped lambda calculus,
applicative bisimilarity and contextual equivalence coincide (Abramsky);
Howe's construction is the standard congruence proof.

For MLTT the situation is not an off-the-shelf Howe theorem:

- types depend on terms, so the relation must be typed and conversion-aware;
- `J`, `case`, and `rec` are not binary application;
- the universe and the eliminators make the congruence proof sensitive to
  type equality;
- the standard tool is a Kripke/step-indexed logical relation, not untyped
  applicative bisimulation.

A **typed, heterogeneous applicative bisimulation** with a **type-directed Howe
closure** is a reasonable research target.  It must relate types and contexts,
not just terms of one type.  It is not a standard result for full MLTT, and the
programme should not assume one until it is proved.

### What the literature actually covers

- Marabelli and Momigliano, *Formalizing Program Equivalences in Dependent Type
  Theory*, formalize **PCFL** — a simply typed lambda calculus with recursion and
  lazy lists — in Coq.  Coq is the dependently typed **meta-language**; the
  object language has no dependent types.  They relate contextual,
  context-less, and applicative similarity.
- Thibodeau, Momigliano, and Pientka, *A Case-Study in Programming Coinductive
  Proofs: Howe's Method*, mechanize Howe for **PCFL** in Beluga.  The dependent
  types of LF/Beluga are again the meta-language, not the object theory.
- Hur, Dreyer, Neis, and Vafeiadis, *The Marriage of Bisimulations and Kripke
  Logical Relations*, combine process bisimulation with Kripke logical relations
  for ML-like imperative languages.  It is not an MLTT result.
- Atkey, Ghani, and Johann, *A Relationally Parametric Model of Dependent Type
  Theory*, build a reflexive-graph/CwF model of predicative and impredicative
  MLTT with `Pi`, `Nat`, and a universe.  It is the closest dependent analogue
  of a logical relation: a parametric model with identity extension, not a
  Howe theorem and not a contextual-equivalence theorem.
- Koutavas, Levy, and Sumii, *Limitations of Applicative Bisimulation*, is the
  cautionary side: applicative bisimulation is not automatically the right
  notion once the language has richer features.

The precise conclusion from the literature reviewed: **there is no standard
off-the-shelf Howe theorem for MLTT as the object language.**  The standard dependent tool is a type-directed
Kripke/reflexive-graph logical relation.  A Howe-style closure is a research
target for a chosen object fragment, not an assumption of the programme.

## 6. The supercompiler's process graph

At the process level, the supercompiler has configurations and transitions:
driving, generalization, folding, residualisation.  A **bisimulation** on that
transition system can relate the source and residual evaluation trees.

The proof obligation is:

```text
process bisimulation R
  => LR at the source type
  => contextual equivalence
```

The first implication is the bridge from the process graph to the object
language; the second is the adequacy of the logical relation.  A Howe-style
closure would be needed if the process relation is to be compositional under
the object-language contexts.

This is a **bisimulation of processes**, not a bisimulation of object terms;
the object equality remains contextual/logical.

## 7. HoTT and transport

In the univalent reading, the residual type `A'` and the source type `A` are
related by an equivalence:

```text
e : A' ≃ A
transport e : A' -> A
```

Type equivalence is a type; transport is its action on terms.  The term-level
correctness is separate:

```text
transport e (sc(t)) ≡ctx t : A
```

or, heterogeneously,

```text
sc(t) ≈ctx_e t : A' ~ A
```

or a path in the identity type when the type theory has one.  Univalence
identifies equivalent types, but it does not identify arbitrary source and
residual terms; the transport and the contextual/logical relation are both
needed.

## 8. Proposed correctness statement

```text
sc : (t : A) -> { A' : Type } × (e : A' ≃ A) × Term A'

correctness :
  for every t : A,
    transport e (sc(t).2) ≡ctx t : A
```

The heterogeneous form is:

```text
sc(t).2 ≈ctx_e t : A' ~ A
```

Both use the same logical relation; the transport form is the specialization at
the source type.

with the proof route:

1. a heterogeneous process bisimulation between source and residual
   configurations at related types;
2. a heterogeneous Kripke logical relation at the source/residual type
   relation;
3. adequacy: logical equivalence implies heterogeneous contextual equivalence;
   same-type contextual equivalence after transport;
4. a type-directed congruence/CIU step; Howe only when the object fragment is
   an applicative lambda calculus;
5. transport coherence at the type level.

## 9. Current boundary

The repository does not yet have:

- a `Conv` relation or a conversion-aware typing judgment;
- a contextual-equivalence definition;
- a Kripke logical relation or its fundamental theorem;
- a process bisimulation, a type-directed Howe closure, or a CIU theorem;
- the term-level supercompiler correctness theorem.

`Orbit.lean` proves connectivity in a graph of typed terms; that is not
contextual equivalence.  `Spec.lean` is the transport schema.  The Cubical
development is the type-level path/equivalence component.

The next honest step is to fix the object-level notion: typed contextual
equivalence for the uniform core, and the logical relation that proves it.
The Howe literature is a guide for the process/congruence layer, not evidence
that the object-level MLTT equivalence already exists.

## 10. References

- G. Marabelli and A. Momigliano. *Formalizing Program Equivalences in
  Dependent Type Theory*.  CEUR Workshop Proceedings 2504, 2019.
  <https://ceur-ws.org/Vol-2504/paper23.pdf>
- D. Thibodeau, A. Momigliano, and B. Pientka. *A Case-Study in Programming
  Coinductive Proofs: Howe's Method*.  Mathematical Structures in Computer
  Science.
  <https://www.cs.mcgill.ca/~dthibo1/papers/howes.pdf>
- R. Atkey, N. Ghani, and P. Johann. *A Relationally Parametric Model of
  Dependent Type Theory*.  POPL 2014.
  <https://bentnib.org/dtt-parametricity.pdf>
- C.-K. Hur, D. Dreyer, G. Neis, and V. Vafeiadis. *The Marriage of
  Bisimulations and Kripke Logical Relations*.  POPL 2012.
  <https://people.mpi-sws.org/~dreyer/papers/marriage/popl.pdf>
- V. Koutavas, P. B. Levy, and E. Sumii. *Limitations of Applicative
  Bisimulation* (preliminary report).  Dagstuhl Seminar Proceedings, 2010.
  <https://drops.dagstuhl.de/storage/16dagstuhl-seminar-proceedings/dsp-vol10351/DagSemProc.10351.4/DagSemProc.10351.4.pdf>
- D. J. Howe. *Proving Congruence of Bisimulation in Functional Programming
  Languages*.  Information and Computation 124(2), 1996.
- A. M. Pitts. *Howe's Method for Higher-Order Languages*.  In *Advanced Topics
  in Bisimulation and Coinduction*, Cambridge University Press, 2011.
Only then can the supercompiler's bisimulation be connected to it.
