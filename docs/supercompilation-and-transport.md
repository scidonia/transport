> **Status.** The interface change described in §1 is implemented:
> `CtxRel` and `TyRel` are `Type`-valued in `Transport/Spec.lean`.  The orbit
> baseline in §4 is `Transport/Orbit.lean`; the first reverse certificate in
> §7 is `Transport/Certificate.lean`; the process-graph derivation is
> `Transport/Derivation.lean`, and the index migration is
> `Transport/IndexMigration.lean`.  Univalence is not axiomatised over
> Lean's `Eq`: `Transport/UnivalenceObstruction.lean` proves the obstruction,
> and the HoTT model reuses `cubical/Univalence.agda`.  The HoTT layer uses
> Cubical Agda's path equality, separate from Lean's `Eq`.  The univalent
> layer is Cubical Agda (`cubical/`); Lean 4 HoTT libraries were surveyed and
> are not part of the active build (`docs/lean-hott-survey.md`); the packing
> and three-vector coherence are `cubical/Packing.agda`; the common-ancestor
> compression is `Transport/CommonAncestor.lean`; the reversal cost model is
> `Transport/Cost.lean`.  The commit reference in §1 records the starting
> point, not the current state.

# Supercompilation at terms and types

## Research question

Which equalities between programs and type families can a specified supercompiler realise, what computations do those equalities induce on inhabitants, and which changes in complexity can its rules explain?

At a term, a supercompiler can turn a symbolic computation into a residual program. At a type, the same process can change the type at which an existing value must be used. A successful transformation of a family from $A(x)$ to $B(x)$ should tell a client how to move an inhabitant from one fibre to the other. If its certificate gives a universe path $p_x : A(x)=_{\mathcal U}B(x)$, dependent transport performs that move. The research problem is to discover which paths driving, generalisation and folding can generate, and to prove what transport along those paths computes.

Three examples set the scope. List reversal tests whether a generaliser can discover a recursive invariant that changes asymptotic cost. Vector packing tests whether two different transformation histories give the same migration for a dependent client. An online queue tests when a faster implementation must leave a specified representation discipline.

## 1. Starting point in this repository

At commit `77c454c`, `Transport.transport_theorem` composes a supplied residual typing theorem with a supplied typed readback operation. Its conclusion says that the transported term has the source type. The concrete instance contracts one outermost β-redex on the `Simple` fragment, with identity context and type translations. The development also has substitution lemmas for the fragment, an object-language typing proof for `J`, and weakening for the equality family. A process graph implementing driving, generalisation, folding and residualisation is an extension proposed here. So are a semantics of observations and a model of computational univalence. [Specification](https://github.com/scidonia/transport/blob/77c454ce7b7638944b3328d21a7180c02e130f4b/Transport/Spec.lean) · [β instance](https://github.com/scidonia/transport/blob/77c454ce7b7638944b3328d21a7180c02e130f4b/Transport/Mltt/Beta.lean) · [Formalisation map](https://github.com/scidonia/transport/blob/77c454ce7b7638944b3328d21a7180c02e130f4b/docs/formalization.md)

The first interface change is to retain transformation witnesses in Lean's `Type`. In the current specification, `CtxRel` and `TyRel` take values in `Prop`, so proofs with the same endpoints are proof-irrelevant. Keep typing and soundness statements in `Prop`. Store the chosen substitution, generalised configuration, fold target, and migration maps as data. Two certificates may share endpoints and still deserve comparison.

## 2. What constitutes a certified transformation?

Fix an object language, evaluation strategy, observable interface and collection of admissible rules $K$. Start with a pure, total, first-order list fragment with structural recursion. Use open configurations so that the result applies to all inputs and can be substituted into a larger client.

| Operation | Data the certificate retains | Obligation |
|---|---|---|
| Drive | Symbolic equation or case split, with refined branch contexts | Reassembling the branches gives the original behaviour for every closing substitution. |
| Generalise | A configuration $G$ in a parameter context and an instantiation for each covered node | Instantiation recovers each original node, up to the equality admitted by $K$. |
| Fold | A back-edge, its target parameters, and a recursive call in the residual worker | The instance matches. The resulting recursion is justified, initially by structural decrease. |
| Residualise | Worker definitions and their entry call | The process graph denotes the source, and the residual program implements that graph uniformly in the parameters. |

This gives a proof-relevant judgement $d:p\Rightarrow_K q$ for a completed transformation. Write $\Rightarrow_K^*$ for finite composition. Its first soundness theorem should quantify over well-typed closing substitutions $\rho$. At a fixed ground interface the conclusion is $\llbracket p[\rho]\rrbracket=\llbracket q[\rho]\rrbracket$. At a changed interface, compare related environments and results through the declared interface relation. For dependent clients, show how the certificate reindexes under substitution, with the necessary equality between the reindexed result types. The residual syntax may differ depending on whether substitution exposes a new redex.

A branch of an open case split has its conclusion in a refined context. A generalised configuration may admit more environments than the original. These facts explain why individual process-graph arrows cannot all be declared equalities between whole programs. The external edge is justified by the completed certificate. Work on multi-result supercompilation gives a useful precedent for retaining the instantiation when rebuilding a configuration. [Klyuchnikov and Romanenko, *Formalizing and Implementing Multi-Result Supercompilation*](https://pat.keldysh.ru/~roman/publications/2012-Klyuchnikov_Romanenko--Formalizing_and_Implementing_Multi-Result_Supercompilation--meta2012.pdf)

## 3. The direct connection to HoTT

### Two equalities

The Lean presentation uses Lean's `Eq` for the object theory and the
metatheory.  That equality is proof-irrelevant, and univalence over it is
inconsistent: the round-trip law forces the identity self-equivalence of `Bool`
to equal negation (`Transport/UnivalenceObstruction.lean`).

The HoTT layer therefore uses Cubical Agda's proof-relevant path equality
`_≡_`, where `ua`, `uaβ`, and `uaIdEquiv` compute
(`cubical/Univalence.agda`).  A `TransportData` over `Eq` is the definitional or
propositional regime; the univalent regime lives over the Cubical path type.
The two equalities are not interchangeable.

### An index transformation moves existing values

Take $i:\mathrm{Fin}(\mathrm{length}(xs\mathbin{++}ys))$. A transformation of the index computation may yield a certificate

$$
h_{xs,ys}:\mathrm{length}(xs\mathbin{++}ys)=\mathrm{length}(xs)+\mathrm{length}(ys).
$$

Applying $\mathrm{Fin}$ to that equality gives a path between types. Transport carries $i$ to the residual type. The target theorem says that the underlying natural number of the transported index equals the underlying natural number of $i$, and that this construction is stable under substitution for $xs,ys$. This case requires identity elimination. It provides a first experiment in the object theory once the required families and equations are available.

### A representation transformation computes a migration

For fixed lengths $m,n$ and a set of elements $A$, consider
$P=\mathrm{Vec}(A,m)\times\mathrm{Vec}(A,n)$ and $V=\mathrm{Vec}(A,m+n)$.
Append and split at $m$ give an equivalence $e:P\simeq V$ once both round-trip laws are proved. Univalence yields $\mathrm{ua}(e):P=_{\mathcal U}V$. The target computation laws are

$$
\mathsf{transport}(\mathrm{ua}(e),(u,v))=\mathsf{append}(u,v),
\qquad
\mathsf{transport}(\mathrm{ua}(e)^{-1},w)=\mathsf{splitAt}(m,w).
$$

Prove these first as propositional equalities. Whether they reduce directly in an implementation is a further question about its computational interpretation and the encoding. An interface with operations also needs proofs that the operations commute with migration. For many-to-one representations, an abstraction relation or quotient can supply the appropriate interface even when the concrete carriers have no such equivalence. [The HoTT Book, chapters 2 and 6](https://homotopytypetheory.org/book/) · [Angiuli et al., *Internalizing Representation Independence with Univalence*](https://arxiv.org/abs/2009.05547)

### The higher-dimensional experiment

Pack three vectors of lengths $l,m,n$ into one. Fix a common source bracketing for the triple. One route first packs the first two vectors. The other first packs the last two. Their result lengths are $(l+m)+n$ and $l+(m+n)$. Use associativity of addition to align the targets, and use the product associator to align the inputs.

The proof has three observable milestones. First prove that append associativity, with the indicated index transport, identifies the resulting vectors for every input triple. Then use function extensionality and the fact that being an equivalence is a proposition to identify the two aligned packing equivalences. Finally apply univalence and its composition laws to obtain a **2-path between the two composite universe paths**. For every dependent family on that universe, transport along the two routes then agrees. A client can change implementations without acquiring a proof obligation about which route the generaliser chose.

This example gives the project a test for the word *higher*. A pair of semantically correct residuals is only the starting data. The result compares their actions on inhabitants and then on dependent clients. The two routes may still perform different amounts of copying.

## 4. Observational topology and the space generated by certificates

Fix an observable program interface. For each closing experiment $C[-]$ and result $v$, let $U_{C,v}=\{p\mid C[p]\Downarrow v\}$. Generate a topology from these positive observations. Its indistinguishability relation is equality of observable profiles. Its specialisation preorder orders programs by inclusion of their positive observations. Counting evaluation steps as an observation changes the equivalence being studied. For the optimisation experiments, take extensional results as the observations and record costs separately. [Escardó, *Topology of data types*](https://people.cs.nott.ac.uk/psztxa/mgs/TOP.html)

Separately, present a homotopy type $X_K$ with a point for each program, a path for each completed certificate, and specified 2-paths for equations between derivations. The directed certificates remain available before this passage to paths. Reversing a path lets one transport a client backwards even when running the supercompiler backwards would be impossible.

Let $O$ be the set of observable profiles. Soundness induces $o_K:X_K\to O$. For behaviour $b$, the fibre $o_K^{-1}(b)$ contains all implementations with profile $b$; its components classify implementations connected by $K$-zigzags. Thus a single observational equivalence class can contain many transformation classes. At types, interpreting certificates as universe paths requires the additional equality or equivalence data of §3. A mere proof that two terms pass the same tests supplies no general operation on arbitrary dependent families.

Four questions can now be asked independently.

| Object | Question |
|---|---|
| Directed derivations from $p$ | Which residuals can this calculus produce? |
| Components of $o_K^{-1}(b)$ | Which implementations of this behaviour share a certified zigzag? |
| Parallel paths between two implementations | Which transformation histories induce equal transports? |
| Concrete costs along forward derivations | Which asymptotic bounds can be attained from this source? |

An immediate baseline is available for the current code. Let $f$ be its deterministic outermost β function, and let $p\sim_f q$ denote connectivity in the undirected graph of $t\to f(t)$. Then

$$
p\sim_f q\quad\Longleftrightarrow\quad\exists m,n,\ f^m(p)=f^n(q).
$$

Forward orbits meeting is an equivalence relation: for transitivity, two meeting points on the middle orbit are ordered by iteration. Each edge satisfies the relation, and a common iterate gives a zigzag. This proof applies to any endofunction, including one with infinite orbits. The terms $\lambda x.\,(\lambda y.\,y)\,x$ and $\lambda x.\,x$ are distinct fixed points of this particular $f$. Adding contraction under a binder connects them immediately. This gives an exact component theorem and a strict enlargement at the first level, without assuming a normalisation theorem for the full object theory.

## 5. Oracle generalisation and common ancestors

A generaliser may be a search procedure, a human-supplied lemma or an oracle. Give the oracle responsibility for proposing a witness. The admissible certificate language determines which witnesses can be checked. Three meanings of a shared node “above” two programs require different evidence.

| Claim about $G$ | Required evidence |
|---|---|
| Both nodes are instances of one configuration | Substitutions $\sigma_p,\sigma_q$ with $G[\sigma_p]=p$ and $G[\sigma_q]=q$ in the chosen equality |
| Both programs descend computationally from one node | Completed derivations $p\leftarrow_K^*G\rightarrow_K^*q$ at the same observable interface |
| The common program is more expensive | A cost inequality on corresponding inputs under a specified evaluator |

A fresh variable generalises both Boolean constants. This explains why a bare common instance pattern has almost no discriminatory power. A successful uniform residualisation of $G$ instead gives a family of edges $G[\sigma]\Rightarrow R[\sigma]$, one for each admissible substitution. At types, if $\alpha_\delta:G(\delta)=A(\delta)$ and $\beta_\delta:G(\delta)=B(\delta)$, then $\alpha_\delta^{-1}\cdot\beta_\delta$ connects the two residual types. For different parameter instances, a path $h:\delta_1=\delta_2$ would provide the missing leg $\mathsf{ap}_G(h)$. The family $\mathrm{Fin}$ alone gives no path between $\mathrm{Fin}(2)$ and $\mathrm{Fin}(3)$.

**Common-ancestor problem.** For which calculi can every finite zigzag be compressed to a single common-ancestor span? A sufficient condition is that whenever $G_1\Rightarrow_K^*r\Leftarrow_K^*G_2$, some $H$ reaches both $G_1$ and $G_2$. This is confluence of the reversed relation. It lets us combine adjacent spans. Test it on a restricted calculus and seek a small non-compressible zigzag when it fails. Require actual derivations at the fixed interface: a new Boolean switch selecting either program at different inputs would trivialise the intended question.

An oracle that improves search while emitting the same certificates changes discovery. A derived lemma can shorten certificates while preserving components. Adjoining a new primitive lemma can merge components or add a parallel path. To prove a strict merger, exhibit an invariant of *all* old zigzags that distinguishes the endpoints. An unsuccessful run of one search strategy establishes much less.

## 6. Hierarchies and complexity

Order calculi by inclusion of their admissible rules. Each inclusion $K\subseteq L$ gives a map $X_K\to X_L$. Study the inclusion-minimal rule sets that reach a target residual or cost bound. Several incomparable minima are possible: a named algebraic lemma and a process-tree transformation may independently make the same worker reachable. For a fixed input-size convention and evaluator, record the forward cost spectrum $\{[T_q]_\Theta\mid p\Rightarrow_K^*q\}$. Charge any representation conversions needed at the observable interface. Record transformation search cost and certificate size separately from residual runtime.

### List reversal tests discovery of an invariant

Start with naïve reverse on immutable lists. Propose $G(xs,a)=\mathsf{reverse}(xs)\mathbin{++}a$. The source is the instance $G(xs,[])$. Driving the cons branch gives

$$
G(x::xs,a)
=(\mathsf{reverse}(xs)\mathbin{++}[x])\mathbin{++}a
=\mathsf{reverse}(xs)\mathbin{++}(x::a)
=G(xs,x::a).
$$

The middle equality uses append associativity. The last equation licenses the fold on a structurally smaller list. The nil branch returns $a$. A uniform proof by induction on $xs$ certifies the accumulating worker for every $a$. Under strict evaluation with full list results and ordinary immutable cons, the source costs $\Theta(n^2)$ and the worker $\Theta(n)$. Both consume and produce the same list representation.

Compare two certificate constructions: introduce the generalisation and associativity lemma explicitly, or derive the residual by transforming process trees. Hamilton's hierarchy derives accumulating reverse at level 2. His level-dependent speedup bound assumes a particular transformer and excludes common-subexpression elimination during generalisation. Repeated passes, a change to sharing, and arbitrary zigzags each require a fresh argument. A derived invariant can explain an improvement without requiring a primitive representation-change rule. [Hamilton, *The Next 700 Program Transformers*, §6](https://arxiv.org/pdf/2108.11347)

### Online queues test necessity of a representation change

Require each update to return a fully realised immutable singly linked list in dequeue order. Use an ordinary pointer machine charging for new cons cells, with fresh input values arriving online. After $k$ enqueues, appending a fresh last value changes the last link, so each of the $k$ existing prefix cells must be rebuilt. Starting from empty, $n$ successive enqueues require $\Omega(n^2)$ work under this discipline. Giving the optimiser the whole batch, introducing delayed links, or admitting mutable tails would change the hypotheses.

Now represent the queue by $(front,rear)$ with abstraction $front\mathbin{++}\mathsf{reverse}(rear)$. Enqueue conses onto the rear. When necessary, dequeue reverses the rear to refill the front. Starting empty and following one linear history, each element changes lists at most once. The potential proportional to $|rear|$ pays for reversal, giving $O(n)$ total work for $n$ operations. The abstraction proof compares observable queues. The amortised proof is about concrete states; quotienting states first would lose the potential.

The pair-of-lists abstraction is many-to-one. Use a relation between representations, or prove equivalence after quotienting by abstract queue equality. Together, the lower and upper bounds give the intended necessity statement: any linear-total-cost solution must leave at least one of the original representation or machine assumptions. They give no necessity result about *who discovers* the representation. [Angiuli et al., queue example](https://arxiv.org/abs/2009.05547)

## 7. Mechanisation and publication targets

| Stage | Deliverable | Criterion for completion |
|---|---|---|
| 1. Components | Lean proof of the orbit theorem and its β instance | Two typed fixed points are disconnected in the initial calculus and connected after adding the binder rule. |
| 2. Supercompilation | A small checker for drive, generalise, fold and residualise certificates | It checks a nontrivial recursive worker; its soundness theorem quantifies over closing substitutions; the fold has an explicit decrease argument. |
| 3. Type-level action | Length-index residualisation and migration of a finite index | The returned index has the announced residual type, preserves its numerical value, and reindexes correctly. |
| 4. HoTT interpretation | Vector packing, unpacking, and the three-vector coherence proof | Transport computes the chosen migration in each direction, and the two packing routes agree on dependent clients. |
| 5. Separation | Reversal cost derivation, queue lower bound, and a common-ancestor result for a named calculus | Distinguish forward attainability, zigzag connectivity and representation hypotheses in each theorem statement. A minimal counterexample to span compression is a result. |

Stages 1–3 can use Lean as the metatheory of an explicit object calculus. For stage 4, a small Cubical Agda model is a practical way to test the universe paths and their computation laws.  Its path equality is separate from Lean's `Eq`: the latter is proof-irrelevant and cannot host univalence (the obstruction above), while the Cubical path type carries `ua`, `uaβ`, and the 2-path coherence data. Specify the interpretation from the Lean presentation to that model; if the link is initially mathematical, label the two checked developments accordingly. Proof-relevant derivation data in Lean do not by themselves confer univalence on the object theory. For stage 5, local coherence results for rewriting suggest how to build equations between histories once the relevant well-foundedness and confluence hypotheses are established. [Kraus and von Raumer, *A Rewriting Coherence Theorem with Applications in Homotopy Type Theory*](https://arxiv.org/abs/2107.01594)

Certifying supercompilation for Martin-Löf type theory already has a substantial precedent in TT Lite SC, which produces residual programs and independently checkable equivalence proofs. A first paper from this programme should exhibit one checked derivation that changes a dependent type, prove what its transport computes, and compare two derivations by a coherence theorem. A subsequent classification result should identify a rule or invariant that strictly changes the reachable residuals or costs. Those results would connect the computational operations of the supercompiler to the geometry of its certificates. [Klyuchnikov and Romanenko, *Certifying Supercompilation for Martin-Löf's Type Theory*](https://pat.keldysh.ru/~klyuchnikov/ttlite-psi2014.pdf)
