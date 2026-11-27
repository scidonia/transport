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

- Jia, Zhao, Sjöberg, and Weirich, *Dependent Types and Program Equivalence*
  (POPL 2010), define a dependently typed language parameterized by an abstract
  term equivalence `isEq`, and instantiate it with a call-by-value contextual
  equivalence `isEqCA` with equivalence assumptions.  This is a genuine
  **contextual equivalence in a dependently typed language**.  Two cautions:
  `isEq` is a relation on **raw terms**, not a typed heterogeneous relation,
  and the paper proves type safety from `isEq` properties, not a Howe theorem.
  It is still the closest precedent for the object-level CIU question.
- Marabelli and Momigliano, *Formalizing Program Equivalences in Dependent Type
  Theory*, formalize **PCFL** — a simply typed lambda calculus with recursion and
  lazy lists — in Coq.  Coq is the dependently typed **meta-language**; the
  object language has no dependent types.  They relate contextual,
  context-less, and applicative similarity.
- Thibodeau, Momigliano, and Pientka, *A Case-Study in Programming Coinductive
  Proofs: Howe's Method*, mechanize Howe for **PCFL** in Beluga.  The dependent
  types of LF/Beluga are again the meta-language, not the object theory.
- Biernacki and Polesiuk, *Logical Relations for Coherence of Effect Subtyping*
  (TLCA 2015), use **heterogeneous typed logical relations** (step-indexed and
  biorthogonal) between different source and target terms/types.  This is direct
  evidence that heterogeneous typed relations are established; it is not MLTT
  and it is not a Howe closure.
- Hur, Dreyer, Neis, and Vafeiadis, *The Marriage of Bisimulations and Kripke
  Logical Relations*, combine process bisimulation with Kripke logical relations
  for ML-like imperative languages.  It is not an MLTT result.
- Hirschowitz and Lafont, *A categorical framework for congruence of applicative
  bisimilarity in higher-order languages*, gives a general categorical account
  of Howe-style congruence; it is not a specific MLTT theorem.
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
- L. Jia, J. Zhao, V. Sjöberg, and S. Weirich. *Dependent Types and Program
  Equivalence*.  POPL 2010.
  <https://www.andrew.cmu.edu/user//liminjia/research/papers/popl10-lambda-eek.pdf>
- D. Biernacki and P. Polesiuk. *Logical Relations for Coherence of Effect
  Subtyping* (TLCA 2015).  <https://drops.dagstuhl.de/storage/00lipics/lipics-vol038-tlca2015/LIPIcs.TLCA.2015.107/LIPIcs.TLCA.2015.107.pdf>
- T. Hirschowitz and A. Lafont. *A categorical framework for congruence of
  applicative bisimilarity in higher-order languages*.  LMCS 18(3), 2022.
  <https://arxiv.org/pdf/2103.16833>
- D. J. Howe. *Proving Congruence of Bisimulation in Functional Programming
  Languages*.  Information and Computation 124(2), 1996.
- A. M. Pitts. *Howe's Method for Higher-Order Languages*.  In *Advanced Topics
  in Bisimulation and Coinduction*, Cambridge University Press, 2011.
Only then can the supercompiler's bisimulation be connected to it.

## 11. Untyped observations and the typed lift

The tempting route is:

```text
erase both programs
prove untyped observational equivalence
somehow lift to typed equivalence
```

That works only in one direction.

### 11.1 Erasure is sound, not complete

Let `erase` map typed terms to an untyped calculus, and assume:

- typed contexts erase to untyped contexts;
- typed observations are the corresponding untyped observations on erased
  terms (termination, normal form, constructor, etc.).

Then, for `t, u : A`:

```text
erase(t) ≡u erase(u)  =>  t ≡ctx u : A
```

because every typed context is an untyped context after erasure, and untyped
equivalence quantifies over **more** contexts.

The converse fails.  Typed contexts are fewer, and type abstraction/parametricity
can identify typed programs that an untyped context distinguishes.  Erasure is a
**sound approximation**, not a characterisation of typed equivalence.

### 11.2 Erasure loses the type relation

For `t : A`, `u : A'` with `R : A ~ A'`, erasure forgets `R` entirely.  Untyped
equivalence may say that the erased programs behave the same, but it does not
establish the type-indexed relation `t ≈_R u`.  In particular, for a function
type it does not establish that related arguments map to related results; that
is a type-directed property.

So the untyped relation is not the general typed relation.  It can prove
soundness at a common erased type; it cannot define the heterogeneous typed
relation.

### 11.3 The typed bridge: a cross-language logical relation

The clean architecture is a **typed logical relation between source and residual
programs**, indexed by a type relation:

```text
LR_{Γ~Γ', A~A'}(t, u)
```

with:

- clauses for `Pi`, `Sigma`, identity, inductive families, and universes;
- stability under weakening/substitution and conversion;
- a fundamental theorem for the source and residual typing judgments;
- adequacy: `LR` implies typed contextual equivalence (heterogeneous, or
  same-type after transport).

The supercompiler proof then has two layers:

1. **Process layer.**  Erase the operational semantics and prove a
   **process bisimulation** between source and residual configurations.  This is
   where an untyped Howe/CIU argument can be used.
2. **Type layer.**  Prove that the process relation is contained in the typed
   logical relation:

   ```text
   process bisimulation  =>  LR_{A~A'}(t, sc(t))
   ```

   and then use adequacy to obtain typed contextual equivalence.

The untyped observation is the **operational model** of the process layer.  The
typed logical relation is the **specification** of the object layer.  The
implication from process bisimulation to `LR` is the typed lift; it is proved by
induction on the type relation and the process graph, not by erasure alone.

### 11.4 Where Howe fits

- At the **untyped/process** level, Howe's method proves the process
  bisimulation is a congruence.
- At the **typed** level, the fundamental theorem of the logical relation is the
  typed congruence theorem.  It is the analogue of Howe's result, but it is
  type-directed and conversion-aware.
- A **heterogeneous typed Howe closure** would be an alternative route to typed
  congruence; it is not required if the logical-relation route is used, and it is
  still a research target for MLTT with conversion/eliminators.

### 11.5 The proof obligation

For `t : A`, `sc(t) : A'`, `e : A' ≃ A`:

```text
erase(t) ≈process erase(sc(t))
  => LR_{A' ~ A}(sc(t), t)
  => sc(t) ≈ctx_e t : A' ~ A
  => transport e (sc(t)) ≡ctx t : A
```

The first arrow is the process bisimulation; the second is the typed lift
(process relation into the logical relation); the third is adequacy; the fourth
is the same-type specialization.

The untyped calculus gives the **observational elements** and the process
bisimulation.  It does not replace the typed logical relation; it feeds it.

## 12. Pullbacks, lifts, and the typed transformation

The typed transformation is primary:

```text
sc_T : (t : A) -> { A' : Type } × (e : A' ≃ A) × Term A'
```

The untyped transformation is its erasure:

```text
erase(sc_T(t)) = sc_U(erase(t))
```

This is a commuting square, not a definition of `sc_T` by pullback:

```text
Typed --sc_T--> Typed
  | erase          | erase
  v                v
Untyped --sc_U--> Untyped
```

### 12.1 The erasure pullback is a relation

Pulling back the graph of `sc_U` along `erase × erase` gives a relation on
typed terms:

```text
R_erase(t,u)  iff  erase(u) = sc_U(erase(t))
```

This is a **relation**, not a function:

- `sc_U(erase(t))` may have several typed liftings, at different types;
- it may have none, unless a typing/lifting theorem is proved;
- the untyped term does not record which typing derivation or which index was
  used.

So the pullback is a **sound candidate relation**, and the graph of the typed
transformation is a **subrelation** of it. It does not induce `sc_T` by itself.
The type-directed algorithm chooses a section; the choice is the typed
transformation.

### 12.2 The typed lift is a section

Think of `erase` as a display/fibration from typed terms to untyped terms. A
typed transformation `sc_T` is a **lift** of `sc_U`:

- its graph is a subobject of the pullback relation;
- for each typed input it selects a typed output and a type equivalence;
- the square commutes by construction.

The pullback gives the **space of possible lifts**; the section gives the
**function**. The existence of the section is the type-preservation theorem,
not a categorical formality.

### 12.3 Where the typed logical relation enters

The correctness of the section is not the pullback; it is the heterogeneous
logical relation:

```text
LR_{A' ~ A}(sc_T(t), t)
```

The proof route is:

1. the typed transformation is defined on typed derivations / the typed
   process graph;
2. its erasure is the untyped transformation, and the square commutes;
3. the untyped process bisimulation relates the erased configurations;
4. the typed logical relation lifts that process relation to the typed level;
5. adequacy gives typed contextual equivalence;
6. transport gives the same-type source theorem.

The pullback is step 2's relation; the logical relation is step 4; they are not
the same object.

### 12.4 Type equivalence is a pullback; the term relation is not just that

For a type equivalence `e : A ≃ A'`, the graph relation

```text
R_e(a,a')  iff  e(a) = a'
```

is the pullback of the identity relation along `e` at the type level. The term
relation at `e` is the corresponding graph/transport relation, but the logical
relation adds the clauses for `Pi`, `Sigma`, identity, and inductive families.
For a general type relation `R : A ~ A'`, the term relation is a subfibration
over `R`, not a single pullback.

### 12.5 Bisimulation and Howe are not pullbacks

- A **bisimulation** is a coalgebraic relation: a relation on configurations
  closed under transitions, with the greatest bisimulation as a coinductive
  fixed point. It is not, in general, a pullback.
- **Howe's closure** is a congruence closure / least compatible relation
  containing a bisimulation; it is a free-algebra construction, not a pullback.
- The typed logical relation is the typed analogue of the congruence theorem.
  A heterogeneous typed Howe closure would be an alternative, not a pullback.

### 12.6 Consequence for the programme

The supercompiler is **type-directed**:

- driving uses the type/index structure;
- the residual type `A'` and equivalence `e` are produced with the residual
  term;
- the untyped process graph is the erasure of the typed process graph;
- the untyped bisimulation is the operational proof of the erased graph;
- the typed logical relation is the object-level correctness proof.

The untyped pullback is a useful **soundness/approximation** layer. It does not
replace the typed transformation, the typed lifting theorem, or the typed
logical relation.
