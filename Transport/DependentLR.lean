import Transport.Mltt.Core

/-!
# Closedness for the core syntax

This file is the preparation layer for an object-language dependent relation:
closed terms, closed type terms, and the closedness predicate on the core `Tm`.

The full Pi relation is not defined here.  The core `Tm` is a nested inductive
(`ind`, `roll`, and `case` carry `List Tm`), and a Pi relation as an inductive
has a non-strictly-positive occurrence.  A future relation needs a separate
dependent syntax or a contextual definition, not this inductive shape.
-/

namespace Transport.DependentLR

open Transport.Mltt

/-- `ClosedAt k t` means every free variable of `t` is below `k`. -/
def ClosedAt (k : Nat) : Tm → Prop
  | .var i => i < k
  | .sort _ => True
  | .pi A B => ClosedAt k A ∧ ClosedAt (k + 1) B
  | .lam A t => ClosedAt k A ∧ ClosedAt (k + 1) t
  | .app t u => ClosedAt k t ∧ ClosedAt k u
  | .fix A t => ClosedAt k A ∧ ClosedAt (k + 1) t
  | .ind _ args => ∀ t ∈ args, ClosedAt k t
  | .roll _ _ args => ∀ t ∈ args, ClosedAt k t
  | .case _ _ scrut C brs =>
      ClosedAt k scrut ∧ ClosedAt (k + 1) C ∧ ∀ b ∈ brs, ClosedAt k b

/-- A closed term. -/
def Closed (t : Tm) : Prop := ClosedAt 0 t

/-- Closed type terms. -/
def ClosedTyAt (k : Nat) : Tm → Prop
  | .var i => i < k
  | .sort _ => True
  | .pi A B => ClosedTyAt k A ∧ ClosedTyAt (k + 1) B
  | _ => False

def ClosedTy (t : Tm) : Prop := ClosedTyAt 0 t

end Transport.DependentLR
