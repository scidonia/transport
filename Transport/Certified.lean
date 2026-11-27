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

end Transport.Certified
