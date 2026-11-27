import Transport.Action
import Transport.Certified

/-!
# The reverse worker as a process instance
-/

namespace Transport.ActionReverse

open Transport.Certified

universe u

def reverseSource (α : Type u) : Transport.Action.Process (List α) where
  Config := SourceConfig α
  step := sstep
  obs := sObs

def reverseResidual (α : Type u) : Transport.Action.Process (List α) where
  Config := ResidualConfig α
  step := rstep
  obs := rObs

theorem reverseBisim {α : Type u} (xs a : List α) :
    ∀ n, Transport.Action.Bisim (reverseSource α) (reverseResidual α) n
      ⟨xs, a⟩ ⟨.rev, xs, a⟩ := by
  intro n
  induction n generalizing xs a with
  | zero => trivial
  | succ n ih =>
      cases xs with
      | nil =>
          simp [Transport.Action.Bisim, reverseSource, reverseResidual,
            sstep, rstep, sObs, rObs]
      | cons x xs =>
          simp [Transport.Action.Bisim, reverseSource, reverseResidual, sstep, rstep]
          exact ih xs (x :: a)

def reverseFold {α : Type u} (x : α) (xs a : List α) :
    Transport.Action.FoldCert (reverseSource α) (reverseResidual α)
      (fun r => r.xs.length) ⟨x :: xs, a⟩ ⟨.rev, x :: xs, a⟩ where
  p' := ⟨xs, x :: a⟩
  q' := ⟨.rev, xs, x :: a⟩
  step_p := rfl
  step_q := rfl
  bisim := reverseBisim (x :: xs) a
  guarded := by simp

def reverseDerivation {α : Type u} : (xs : List α) → (a : List α) →
    Transport.Action.Derivation (reverseSource α) (reverseResidual α)
      (fun r => r.xs.length) ⟨xs, a⟩ ⟨.rev, xs, a⟩
  | [], a =>
      Transport.Action.Derivation.halt
        (P := reverseSource α) (Q := reverseResidual α)
        (measure := fun r => r.xs.length)
        ⟨[], a⟩ ⟨.rev, [], a⟩ rfl rfl rfl
  | x :: xs, a =>
      Transport.Action.Derivation.fold
        (P := reverseSource α) (Q := reverseResidual α)
        (measure := fun r => r.xs.length)
        ⟨x :: xs, a⟩ ⟨.rev, x :: xs, a⟩
        (reverseFold x xs a)
        (reverseDerivation xs (x :: a))

theorem reverseDerivation_sound {α : Type u} (xs a : List α) :
    ∀ n, Transport.Action.Bisim (reverseSource α) (reverseResidual α) n
      ⟨xs, a⟩ ⟨.rev, xs, a⟩ :=
  Transport.Action.Derivation.sound (reverseDerivation xs a)

end Transport.ActionReverse
