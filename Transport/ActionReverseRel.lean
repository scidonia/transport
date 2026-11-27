import Transport.ActionRel
import Transport.ActionReverse
import Transport.Certified

/-!
# The reverse worker at the list logical relation
-/

namespace Transport.ActionReverseRel

open Transport.Certified

universe u

theorem reverseBisimRel {α : Type u} (xs a : List α) :
    ∀ n, Transport.ActionRel.BisimRel (ListRel Eq)
      (Transport.ActionReverse.reverseSource α)
      (Transport.ActionReverse.reverseResidual α) n
      ⟨xs, a⟩ ⟨.rev, xs, a⟩ := by
  intro n
  induction n generalizing xs a with
  | zero => trivial
  | succ n ih =>
      cases xs with
      | nil =>
          simp [Transport.ActionRel.BisimRel, Transport.ActionReverse.reverseSource,
            Transport.ActionReverse.reverseResidual, sstep, rstep, sObs, rObs]
          exact ListRel.eq_refl a
      | cons x xs =>
          simp [Transport.ActionRel.BisimRel, Transport.ActionReverse.reverseSource,
            Transport.ActionReverse.reverseResidual, sstep, rstep]
          exact ih xs (x :: a)

def reverseFoldRel {α : Type u} (x : α) (xs a : List α) :
    Transport.ActionRel.FoldCertRel (ListRel Eq)
      (Transport.ActionReverse.reverseSource α)
      (Transport.ActionReverse.reverseResidual α)
      (fun r => r.xs.length) ⟨x :: xs, a⟩ ⟨.rev, x :: xs, a⟩ where
  p' := ⟨xs, x :: a⟩
  q' := ⟨.rev, xs, x :: a⟩
  step_p := rfl
  step_q := rfl
  bisim := reverseBisimRel (x :: xs) a
  guarded := by simp

def reverseGenCertRel {α : Type u} (s : SourceConfig α) :
    Transport.ActionRel.GenCertRel (ListRel Eq)
      (Transport.ActionReverse.reverseSource α)
      (Transport.ActionReverse.reverseResidual α) (List α) where
  source := fun a => ⟨s.xs, a⟩
  schema := fun a => ⟨.rev, s.xs, a⟩
  sound := fun a n => reverseBisimRel s.xs a n

def reverseDerivationRel {α : Type u} : (xs : List α) → (a : List α) →
    Transport.ActionRel.DerivationRel (ListRel Eq)
      (Transport.ActionReverse.reverseSource α)
      (Transport.ActionReverse.reverseResidual α)
      (fun r => r.xs.length) ⟨xs, a⟩ ⟨.rev, xs, a⟩
  | [], a =>
      Transport.ActionRel.DerivationRel.halt
        (rel := ListRel Eq)
        (P := Transport.ActionReverse.reverseSource α)
        (Q := Transport.ActionReverse.reverseResidual α)
        (measure := fun r => r.xs.length)
        ⟨[], a⟩ ⟨.rev, [], a⟩ rfl rfl (reverseBisimRel [] a 1)
  | x :: xs, a =>
      Transport.ActionRel.DerivationRel.fold
        (rel := ListRel Eq)
        (P := Transport.ActionReverse.reverseSource α)
        (Q := Transport.ActionReverse.reverseResidual α)
        (measure := fun r => r.xs.length)
        ⟨x :: xs, a⟩ ⟨.rev, x :: xs, a⟩
        (reverseFoldRel x xs a)
        (reverseDerivationRel xs (x :: a))

def reverseGeneralisedRel {α : Type u} (s : SourceConfig α) :
    Transport.ActionRel.DerivationRel (ListRel Eq)
      (Transport.ActionReverse.reverseSource α)
      (Transport.ActionReverse.reverseResidual α)
      (fun r => r.xs.length) s ⟨.rev, s.xs, s.a⟩ :=
  Transport.ActionRel.DerivationRel.generalise
    (rel := ListRel Eq)
    (P := Transport.ActionReverse.reverseSource α)
    (Q := Transport.ActionReverse.reverseResidual α)
    (measure := fun r => r.xs.length)
    s (reverseGenCertRel s) s.a rfl (reverseDerivationRel s.xs s.a)

theorem reverseGeneralisedRel_sound {α : Type u} (s : SourceConfig α) :
    ∀ n, Transport.ActionRel.BisimRel (ListRel Eq)
      (Transport.ActionReverse.reverseSource α)
      (Transport.ActionReverse.reverseResidual α) n
      s ⟨.rev, s.xs, s.a⟩ :=
  Transport.ActionRel.DerivationRel.sound (reverseGeneralisedRel s)

end Transport.ActionReverseRel
