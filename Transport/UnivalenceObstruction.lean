import Std

/-!
# Why univalence is not an axiom over Lean's `Eq`

Lean's identity type is a proposition: `a = b : Prop`, so any two proofs of the
same equality are equal.  Univalence, on the other hand, says that the type of
equivalences `A ≃ B` is itself equivalent to the identity type `A = B`.  The
round-trip law then forces every self-equivalence of a type to be equal.

For `Bool` there are two distinct self-equivalences, the identity and negation.
The theorem below shows that no function `ua : (A ≃ B) → (A = B)` together with
the round-trip law can exist.  So univalence is not merely missing from Lean's
axioms: adding it over the proof-irrelevant `Eq` is inconsistent.

A faithful development needs a proof-relevant path type, as in cubical type
theory.  Stage 4 of the research programme uses Cubical Agda for that reason.
-/

namespace Transport.Obstruction

universe u

/-- A minimal type equivalence. -/
structure Equiv (A B : Type u) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a : A, invFun (toFun a) = a
  right_inv : ∀ b : B, toFun (invFun b) = b

namespace Equiv

/-- The identity equivalence. -/
def refl (A : Type u) : Equiv A A where
  toFun := fun a => a
  invFun := fun a => a
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Transport the identity equivalence along an equality. -/
def ofEq {A B : Type u} (h : A = B) : Equiv A B := by
  cases h
  exact refl A

end Equiv

/-- The identity self-equivalence of `Bool`. -/
def boolId : Equiv Bool Bool := Equiv.refl Bool

/-- Negation as a self-equivalence of `Bool`. -/
def boolNot : Equiv Bool Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := by
    intro b
    cases b <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl

theorem boolId_ne_boolNot : boolId ≠ boolNot := by
  intro h
  have hfun : boolId.toFun = boolNot.toFun := congrArg Equiv.toFun h
  have htrue : boolId.toFun true = boolNot.toFun true := congrFun hfun true
  simp [boolId, boolNot, Equiv.refl] at htrue

/-- No univalence data exists over a proof-irrelevant identity type: a map from
equivalences to equalities cannot have the round-trip law. -/
theorem no_univalence_with_proof_irrelevant_eq
    (ua : ∀ {A B : Type}, Equiv A B → A = B)
    (ua_round : ∀ {A B : Type} (e : Equiv A B), Equiv.ofEq (ua e) = e) :
    False := by
  -- `ua boolNot` is a proof of `Bool = Bool`.  Transporting the identity
  -- equivalence along it reduces to the identity equivalence, because `Eq` is
  -- proof-irrelevant.  The round-trip law then says the identity equivalence
  -- equals negation.
  exact boolId_ne_boolNot (ua_round boolNot)

end Transport.Obstruction
