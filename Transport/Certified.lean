import Transport.Derivation

/-!
# Stage 1: a proof-carrying fold

The residual program has a recursive label `rev`.  `run` is its fuel-indexed
operational semantics.  `Bisim n c` says that `n` steps of the label on `c`
agree with the source worker `revAcc`.  `FoldCert` packages the label step,
its unfolding, the step-indexed bisimulation, and the guarded decrease.
-/

namespace Transport.Certified

open Transport.Certificate
open Transport.Derivation

universe u

/-- Residual-program labels.  The reverse worker is the first one. -/
inductive Label where
  | rev
  deriving Repr

/-- One step of the labelled residual program. -/
def step {α : Type u} : Config α → Option (Config α)
  | ⟨[], _⟩ => none
  | ⟨x :: xs, a⟩ => some ⟨xs, x :: a⟩

/-- Fuel-indexed semantics of the residual label. -/
def run {α : Type u} : Nat → Config α → Option (List α)
  | 0, _ => none
  | _ + 1, ⟨[], a⟩ => some a
  | n + 1, ⟨x :: xs, a⟩ => run n ⟨xs, x :: a⟩

/-- Fuel-indexed agreement between the label and the source worker. -/
def Bisim {α : Type u} (n : Nat) (c : Config α) : Prop :=
  match run n c with
  | some r => r = revAcc c.xs c.a
  | none => True

theorem bisim_zero {α : Type u} (c : Config α) : Bisim 0 c := by
  simp [Bisim, run]

theorem bisim_all {α : Type u} (c : Config α) : ∀ n, Bisim n c := by
  intro n
  induction n generalizing c with
  | zero => simp [Bisim, run]
  | succ n ih =>
      cases c with
      | mk xs a =>
          cases xs with
          | nil => simp [Bisim, run, revAcc_nil]
          | cons x xs =>
              simpa [Bisim, run, revAcc_cons] using (ih ⟨xs, x :: a⟩)

/-- A fold certificate: the label step, its unfolding, the step-indexed
bisimulation, and the guarded decrease. -/
structure FoldCert {α : Type u} (c c' : Config α) where
  label : Label
  step_eq : step c = some c'
  unfold : Config α
  unfold_eq : unfold = c'
  bisim : ∀ n, Bisim n c
  guarded : c'.xs.length < c.xs.length

/-- The recursive reverse label folds a nonempty configuration. -/
def reverseFold {α : Type u} (x : α) (xs a : List α) :
    FoldCert ⟨x :: xs, a⟩ ⟨xs, x :: a⟩ where
  label := .rev
  step_eq := rfl
  unfold := ⟨xs, x :: a⟩
  unfold_eq := rfl
  bisim := bisim_all _
  guarded := by simp

/-- The full run of the label computes the worker. -/
theorem run_sound {α : Type u} (xs a : List α) :
    run (xs.length + 1) ⟨xs, a⟩ = some (revAcc xs a) := by
  induction xs generalizing a with
  | nil => simp [run, revAcc_nil]
  | cons x xs ih =>
      simp [run, ih, revAcc_cons]

/-- The residual program returns the source reverse. -/
theorem residual_sound {α : Type u} (xs : List α) :
    run (xs.length + 1) ⟨xs, []⟩ = some xs.reverse := by
  rw [run_sound, revAcc_reverse]


/-! ## An independent residual label

The residual label has its own configurations and step relation.  The source
worker and the residual label are related by a step-indexed bisimulation.
-/

structure SourceConfig (α : Type u) where
  xs : List α
  a : List α

structure ResidualConfig (α : Type u) where
  label : Label
  xs : List α
  a : List α

def sstep {α : Type u} : SourceConfig α → Option (SourceConfig α)
  | ⟨[], _⟩ => none
  | ⟨x :: xs, a⟩ => some ⟨xs, x :: a⟩

def rstep {α : Type u} : ResidualConfig α → Option (ResidualConfig α)
  | ⟨.rev, [], _⟩ => none
  | ⟨.rev, x :: xs, a⟩ => some ⟨.rev, xs, x :: a⟩

def sObs {α : Type u} : SourceConfig α → Option (List α)
  | ⟨[], a⟩ => some a
  | _ => none

def rObs {α : Type u} : ResidualConfig α → Option (List α)
  | ⟨.rev, [], a⟩ => some a
  | _ => none

def R {α : Type u} (s : SourceConfig α) (r : ResidualConfig α) : Prop :=
  s.xs = r.xs ∧ s.a = r.a

def SBisim {α : Type u} : Nat → SourceConfig α → ResidualConfig α → Prop
  | 0, _, _ => True
  | n + 1, s, r =>
      match sstep s, rstep r with
      | none, none => sObs s = rObs r
      | some s', some r' => SBisim n s' r'
      | _, _ => False

theorem R_bisim {α : Type u} {s : SourceConfig α} {r : ResidualConfig α}
    (h : R s r) : ∀ n, SBisim n s r := by
  intro n
  induction n generalizing s r with
  | zero => trivial
  | succ n ih =>
      rcases s with ⟨sxs, sa⟩
      rcases r with ⟨rlabel, rxs, ra⟩
      cases rlabel
      rcases h with ⟨hxs, ha⟩
      rcases hxs with rfl
      rcases ha with rfl
      cases sxs with
      | nil => simp [SBisim, sstep, rstep, sObs, rObs]
      | cons x xs =>
          simp [SBisim, sstep, rstep]
          exact ih ⟨rfl, rfl⟩

def rrun {α : Type u} : Nat → ResidualConfig α → Option (List α)
  | 0, _ => none
  | _ + 1, ⟨.rev, [], a⟩ => some a
  | n + 1, ⟨.rev, x :: xs, a⟩ => rrun n ⟨.rev, xs, x :: a⟩

theorem rrun_sound {α : Type u} (xs a : List α) :
    rrun (xs.length + 1) ⟨.rev, xs, a⟩ = some (revAcc xs a) := by
  induction xs generalizing a with
  | nil => simp [rrun, revAcc_nil]
  | cons x xs ih => simp [rrun, ih, revAcc_cons]

theorem residual_run {α : Type u} (xs : List α) :
    rrun (xs.length + 1) ⟨.rev, xs, []⟩ = some xs.reverse := by
  rw [rrun_sound, revAcc_reverse]

structure ResidualFoldCert {α : Type u} (s : SourceConfig α)
    (r : ResidualConfig α) where
  source_unfold : SourceConfig α
  source_step_eq : sstep s = some source_unfold
  unfold : ResidualConfig α
  step_eq : rstep r = some unfold
  bisim : ∀ n, SBisim n s r
  guarded : unfold.xs.length < r.xs.length

def residualFold {α : Type u} (x : α) (xs a : List α) :
    ResidualFoldCert ⟨x :: xs, a⟩ ⟨.rev, x :: xs, a⟩ where
  source_unfold := ⟨xs, x :: a⟩
  source_step_eq := rfl
  unfold := ⟨.rev, xs, x :: a⟩
  step_eq := rfl
  bisim := R_bisim ⟨rfl, rfl⟩
  guarded := by simp


/-! ## Stage 2: a generalisation certificate

`GenCert` generalises the source worker over the accumulator.  The schema is a
family of residual configurations; the soundness field is the step-indexed
bisimulation for every instance.  An algorithmic or oracular generaliser must
produce this structure; the proof is checked.
-/

structure GenCert {α : Type u} (s : SourceConfig α) where
  schema : List α → ResidualConfig α
  sound : ∀ a, ∀ n, SBisim n ⟨s.xs, a⟩ (schema a)

/-- The algorithmic generaliser: the accumulator is the schema parameter. -/
def algorithmicGen {α : Type u} (s : SourceConfig α) : GenCert s where
  schema := fun a => ⟨.rev, s.xs, a⟩
  sound := fun a n =>
    R_bisim (s := ⟨s.xs, a⟩) (r := ⟨.rev, s.xs, a⟩) ⟨rfl, rfl⟩ n

/-- The certificate at the source instance. -/
theorem genCert_instance {α : Type u} {s : SourceConfig α} (g : GenCert s) :
    ∀ n, SBisim n s (g.schema s.a) := by
  intro n
  simpa using g.sound s.a n


/-! ## Stage 3: the supercompiler derivation -/

inductive RDerivation {α : Type u} : SourceConfig α → ResidualConfig α → Type u
  | halt (s : SourceConfig α) (r : ResidualConfig α)
      (hxs : s.xs = []) (rxs : r.xs = []) (ha : s.a = r.a) :
      RDerivation s r
  | cert (s : SourceConfig α) (r : ResidualConfig α)
      (h : ∀ n, SBisim n s r) : RDerivation s r
  | generalise (s : SourceConfig α) (g : GenCert s)
      (rest : RDerivation s (g.schema s.a)) :
      RDerivation s (g.schema s.a)
  | fold (s : SourceConfig α) (r : ResidualConfig α)
      (cert : ResidualFoldCert s r)
      (rest : RDerivation cert.source_unfold cert.unfold) :
      RDerivation s r

namespace RDerivation

theorem sound {α : Type u} {s : SourceConfig α} {r : ResidualConfig α}
    (d : RDerivation s r) : ∀ n, SBisim n s r := by
  induction d with
  | halt s r hxs rxs ha =>
      intro n
      cases n with
      | zero => trivial
      | succ n =>
          rcases s with ⟨sxs, sa⟩
          rcases r with ⟨rlabel, rxs, ra⟩
          cases rlabel
          simp at hxs rxs ha
          rcases hxs with rfl
          rcases rxs with rfl
          rcases ha with rfl
          simp [SBisim, sstep, rstep, sObs, rObs]
  | cert s r h => exact h
  | generalise s g rest ih =>
      intro n
      exact g.sound s.a n
  | fold s r cert rest ih =>
      exact cert.bisim

end RDerivation

/-- A generalisation action: the certificate is the GenCert at its instance. -/
def generaliseDerivation {α : Type u} (s : SourceConfig α) (g : GenCert s) :
    RDerivation s (g.schema s.a) :=
  .generalise s g (.cert s (g.schema s.a) (fun n => g.sound s.a n))

/-- The reverse supercompiler: fold on each cons, residualise on nil. -/
def reverseDerivation {α : Type u} : (xs : List α) → (a : List α) →
    RDerivation ⟨xs, a⟩ ⟨.rev, xs, a⟩
  | [], a => .halt ⟨[], a⟩ ⟨.rev, [], a⟩ rfl rfl rfl
  | x :: xs, a =>
      .fold ⟨x :: xs, a⟩ ⟨.rev, x :: xs, a⟩
        (residualFold x xs a)
        (reverseDerivation xs (x :: a))

/-- The top-level certificate carried by the reverse derivation. -/
theorem reverseDerivation_sound {α : Type u} (xs a : List α) :
    ∀ n, SBisim n ⟨xs, a⟩ ⟨.rev, xs, a⟩ :=
  RDerivation.sound (reverseDerivation xs a)

/-- A composed transform: accumulator generalisation followed by the reverse
fold/residualise derivation. -/
def reverseGeneralised {α : Type u} (s : SourceConfig α) :
    RDerivation s ⟨.rev, s.xs, s.a⟩ :=
  .generalise s (algorithmicGen s) (reverseDerivation s.xs s.a)


/-! ## Stage 4, base case: a heterogeneous logical relation for lists -/

inductive ListRel {α β : Type u} (R : α → β → Prop) :
    List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a b : _} {xs ys : _} :
      R a b → ListRel R xs ys → ListRel R (a :: xs) (b :: ys)

theorem ListRel.eq_refl {α : Type u} (xs : List α) : ListRel Eq xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons rfl ih

/-- The source reverse is related to its result at the list logical relation. -/
theorem reverse_LR {α : Type u} (xs : List α) :
    ListRel Eq (revAcc xs []) xs.reverse := by
  rw [revAcc_reverse]
  exact ListRel.eq_refl _

/-- The residual run is related to the source at the same list relation. -/
theorem reverse_residual_LR {α : Type u} (xs : List α) :
    ListRel Eq (revAcc xs [])
      (Option.getD (rrun (xs.length + 1) ⟨.rev, xs, []⟩) []) := by
  rw [residual_run]
  simpa [Option.getD] using reverse_LR (α := α) xs

end Transport.Certified
