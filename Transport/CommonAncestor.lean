import Std

/-!
# Common ancestors and zigzag compression

Stage 5 of the research programme.  A zigzag is a path that may use steps in
either direction.  If the reverse relation is confluent — every two paths into
a common descendant have a common ancestor — then every zigzag compresses to a
span `q ←* H →* p`.

The concrete instance is the successor calculus on `Nat`: every two numbers
that reach a common value have a common ancestor, namely the smaller one.
-/

namespace Transport.CommonAncestor

universe u

variable {α : Type u}

/-- Forward reflexive-transitive closure. -/
inductive Star (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : Star R a a
  | step {a b c : α} : R a b → Star R b c → Star R a c

namespace Star

/-- A single step is a star. -/
theorem single {R : α → α → Prop} {a b : α} (h : R a b) : Star R a b :=
  .step h (.refl b)

/-- Transitivity of the star. -/
theorem trans {R : α → α → Prop} {a b c : α}
    (h1 : Star R a b) (h2 : Star R b c) : Star R a c := by
  induction h1 with
  | refl _ => exact h2
  | step h _ ih => exact .step h (ih h2)

end Star

/-- A zigzag uses steps in either direction. -/
inductive Zigzag (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : Zigzag R a a
  | fwd {a b c : α} : R a b → Zigzag R b c → Zigzag R a c
  | bwd {a b c : α} : R b a → Zigzag R b c → Zigzag R a c

/-- A common ancestor reaches both endpoints. -/
def CommonAncestor (R : α → α → Prop) (p q : α) : Prop :=
  ∃ h, Star R h p ∧ Star R h q

/-- Every two paths into a common descendant have a common ancestor:
confluence of the reversed relation. -/
def CoConfluent (R : α → α → Prop) : Prop :=
  ∀ {p q r : α}, Star R p r → Star R q r → CommonAncestor R p q

/-- Reverse confluence compresses every zigzag to a common-ancestor span. -/
theorem zigzag_compress {R : α → α → Prop} (hc : CoConfluent R) :
    ∀ {p q : α}, Zigzag R p q → CommonAncestor R p q := by
  intro p q h
  induction h with
  | refl a => exact ⟨a, .refl a, .refl a⟩
  | fwd hstep _ ih =>
      rcases ih with ⟨h, hh_b, hh_c⟩
      rcases hc (Star.single hstep) hh_b with ⟨h', hh'_a, hh'_h⟩
      exact ⟨h', hh'_a, Star.trans hh'_h hh_c⟩
  | bwd hstep _ ih =>
      rcases ih with ⟨h, hh_b, hh_c⟩
      exact ⟨h, Star.trans hh_b (Star.single hstep), hh_c⟩

/-! ## The successor calculus -/

/-- One successor step on `Nat`. -/
def Succ (a b : Nat) : Prop := b = a + 1

/-- The star of the successor relation is “adds a natural number”. -/
theorem star_succ_iff {p r : Nat} : Star Succ p r ↔ ∃ k, r = p + k := by
  constructor
  · intro h
    induction h with
    | refl a => exact ⟨0, by omega⟩
    | step h _ ih =>
        rcases ih with ⟨k, hk⟩
        exact ⟨k + 1, by unfold Succ at h; omega⟩
  · rintro ⟨k, rfl⟩
    induction k with
    | zero => exact .refl p
    | succ k ih =>
        exact Star.trans ih (Star.single (by unfold Succ; omega))

/-- The successor calculus is reverse-confluent: the smaller number is the
common ancestor. -/
theorem succ_coconfluent : CoConfluent Succ := by
  intro p q r hp hq
  rcases (star_succ_iff.mp hp) with ⟨k, hk⟩
  rcases (star_succ_iff.mp hq) with ⟨l, hl⟩
  by_cases hpq : p ≤ q
  · refine ⟨p, .refl p, star_succ_iff.mpr ⟨q - p, by omega⟩⟩
  · have hqp : q ≤ p := by omega
    refine ⟨q, star_succ_iff.mpr ⟨p - q, by omega⟩, .refl q⟩

/-- Stage 5 instance: every zigzag in the successor calculus compresses to a
span. -/
theorem succ_zigzag_compress {p q : Nat} (h : Zigzag Succ p q) :
    CommonAncestor Succ p q :=
  zigzag_compress succ_coconfluent h

end Transport.CommonAncestor
