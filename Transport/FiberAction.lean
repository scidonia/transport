import Transport.ActionRel

/-!
# Fibered action relations

`ActionRel` uses one result relation `rel : S -> R -> Prop`.  A dependent
function type needs a family of relations indexed by the argument.  This module
lifts the action calculus to such a family.

A `FiberRel` is an index type with source and residual families and a relation
at each pair of indices.  `FiberBisim` is the per-index `BisimRel`; the fold,
generalisation, and derivation certificates are the corresponding `ActionRel`
structures instantiated at the fiber relation.
-/

namespace Transport.FiberAction

open Transport.Action
open Transport.ActionRel

universe u

/-- An indexed family of result relations. -/
structure FiberRel where
  Index : Type u
  Source : Index → Type u
  Residual : Index → Type u
  rel : (i i' : Index) → Source i → Residual i' → Prop

/-- The bisimulation at one fiber. -/
def FiberBisim (F : FiberRel)
    (P : (i : F.Index) → Process (F.Source i))
    (Q : (i : F.Index) → Process (F.Residual i))
    (i i' : F.Index) : Nat → (P i).Config → (Q i').Config → Prop :=
  BisimRel (F.rel i i') (P i) (Q i')

/-- The fold certificate at one fiber. -/
abbrev FiberFoldCert (F : FiberRel)
    (P : (i : F.Index) → Process (F.Source i))
    (Q : (i : F.Index) → Process (F.Residual i))
    (measure : (i : F.Index) → (Q i).Config → Nat)
    (i i' : F.Index) (p : (P i).Config) (q : (Q i').Config) : Type u :=
  FoldCertRel (F.rel i i') (P i) (Q i') (measure i') p q

/-- The generalisation certificate at one fiber. -/
abbrev FiberGenCert (F : FiberRel)
    (P : (i : F.Index) → Process (F.Source i))
    (Q : (i : F.Index) → Process (F.Residual i))
    (i i' : F.Index) (Params : Type u) : Type u :=
  GenCertRel (F.rel i i') (P i) (Q i') Params

/-- The derivation certificate at one fiber. -/
abbrev FiberDerivation (F : FiberRel)
    (P : (i : F.Index) → Process (F.Source i))
    (Q : (i : F.Index) → Process (F.Residual i))
    (measure : (i : F.Index) → (Q i).Config → Nat)
    (i i' : F.Index) (p : (P i).Config) (q : (Q i').Config) : Type (u + 1) :=
  DerivationRel (F.rel i i') (P i) (Q i') (measure i') p q

/-- A fibered derivation is sound at its fiber. -/
theorem FiberDerivation.sound (F : FiberRel)
    (P : (i : F.Index) → Process (F.Source i))
    (Q : (i : F.Index) → Process (F.Residual i))
    (measure : (i : F.Index) → (Q i).Config → Nat)
    (i i' : F.Index) (p : (P i).Config) (q : (Q i').Config)
    (d : FiberDerivation F P Q measure i i' p q) :
    ∀ n, FiberBisim F P Q i i' n p q :=
  DerivationRel.sound d

end Transport.FiberAction
