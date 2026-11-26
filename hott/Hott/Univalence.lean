import GroundZero.Theorems.Univalence

/-!
# Reused Lean univalence

Ground Zero supplies a proof-relevant `Id`/`Path` type and `ua`/`uaβ` over it.
This is the "different equality" route: it is not Lean's proof-irrelevant
`Eq`, and the obstruction in `Transport/UnivalenceObstruction.lean` does not
apply.

The example is the identity equivalence; a nontrivial migration is a further
use of the same `ua`.
-/

open GroundZero
open GroundZero.Types.Equiv

/-- The marker instance that the `hott` command normally supplies as a local
variable.  Ground Zero is axiomatic HoTT; this is not a new mathematical
assumption beyond its `ua` axiom. -/
axiom groundZeroInstance : GroundZero
attribute [instance] groundZeroInstance

noncomputable section

/-- Univalence of the identity equivalence: the identity path. -/
example {A : Type} : A = A := ua (ideqv A)

/-- The computation rule for the identity equivalence. -/
example {A : Type} (a : A) :
    transportconst (ua (ideqv A)) a = a :=
  uaβ (ideqv A) a

end
