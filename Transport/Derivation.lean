import Transport.Certificate

/-!
# A drive/fold/residualise derivation

The first certificate in `Transport.Certificate` checks the generalisation and
the worker.  This file adds the process-graph part: a configuration, an edge
for each operation, and a derivation whose type is the certificate.  Lean's
kernel is the checker; there is no separate reflection.

The reverse worker is derived for every input and accumulator, so the
soundness theorem quantifies over all closing substitutions.
-/

namespace Transport.Derivation

open Transport.Certificate

universe u

/-- A configuration of the reverse worker: the remaining input and the
accumulator. -/
structure Config (α : Type u) where
  xs : List α
  a : List α

namespace Config

/-- The meaning of a configuration: `reverse xs ++ a`. -/
def denote {α : Type u} (c : Config α) : List α :=
  c.xs.reverse ++ c.a

end Config

/-- A single checked operation.  The type indices are the source and target
configurations, so an edge cannot be applied to the wrong configuration. -/
inductive Edge {α : Type u} : Config α → Config α → Type u
  | driveNil (a : List α) :
      Edge ⟨[], a⟩ ⟨[], a⟩
  | driveCons (x : α) (xs a : List α) :
      Edge ⟨x :: xs, a⟩ ⟨xs, x :: a⟩
  | fold (x : α) (xs a : List α) :
      Edge ⟨x :: xs, a⟩ ⟨xs, x :: a⟩
  | residualise (xs a : List α) :
      Edge ⟨xs, a⟩ ⟨xs, a⟩

namespace Edge

/-- Every edge preserves the meaning of the configuration. -/
theorem sound {α : Type u} {c c' : Config α} (e : Edge c c') :
    c.denote = c'.denote := by
  cases e <;> simp [Config.denote, List.reverse_cons, List.append_assoc]

/-- The fold's explicit decrease: the recursive input is a proper subterm. -/
theorem fold_decrease {α : Type u} (x : α) (xs a : List α) :
    (⟨xs, x :: a⟩ : Config α).xs.length <
      (⟨x :: xs, a⟩ : Config α).xs.length := by
  simp

end Edge

/-- A finite derivation from one configuration to another. -/
inductive Derivation {α : Type u} : Config α → Config α → Type u
  | nil : Derivation c c
  | cons : Edge c c' → Derivation c' c'' → Derivation c c''

namespace Derivation

/-- Soundness of a derivation, by composing the edge soundness theorems. -/
theorem sound {α : Type u} {c c' : Config α} (d : Derivation c c') :
    c.denote = c'.denote := by
  induction d with
  | nil => rfl
  | cons e d ih =>
      rw [Edge.sound e, ih]

end Derivation

namespace Reverse

/-- The derivation of the accumulator worker for every input and accumulator.
Each cons is a fold edge; the nil case residualises. -/
def derivation {α : Type u} : (xs : List α) → (a : List α) →
    Derivation ⟨xs, a⟩ ⟨[], Transport.Certificate.revAcc xs a⟩
  | [], a => .cons (.residualise [] a) .nil
  | x :: xs, a => .cons (.fold x xs a) (derivation xs (x :: a))

/-- The derived worker has the source meaning for every closing substitution. -/
theorem derivation_sound {α : Type u} (xs a : List α) :
    (⟨xs, a⟩ : Config α).denote =
      (⟨[], Transport.Certificate.revAcc xs a⟩ : Config α).denote :=
  Derivation.sound (derivation xs a)

/-- The entry call of the residual worker returns the source value. -/
theorem derivation_residual {α : Type u} (xs : List α) :
    Transport.Certificate.revAcc xs [] = (⟨xs, []⟩ : Config α).denote := by
  simpa [Config.denote] using (derivation_sound xs []).symm

end Reverse

end Transport.Derivation
