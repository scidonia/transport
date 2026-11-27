import Std

/-!
# A first dependent Pi certificate

This is the semantic Pi clause for a heterogeneous dependent function type.
For index types `A` and `A'` with a relation `relA`, families `B` and `B'`,
and a fiberwise relation `relB`, a certificate for `f` and `f'` is a dependent
function:

```text
∀ a a', relA a a' -> relB r (f a) (f' a')
```

The concrete instance is polymorphic identity at `Π A : Type. A → A`, related
across a type equivalence.  This is a semantic model, not yet the object-language
`HasTypeDep` Pi.
-/

namespace Transport.DependentPi

universe u v

/-- A type equivalence, kept explicit so the type relation is heterogeneous. -/
structure Equiv (A B : Type u) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- The fiberwise certificate at a heterogeneous dependent function type. -/
def PiCert {A : Type u} {A' : Type u}
    (relA : A → A' → Prop)
    (B : A → Type v) (B' : A' → Type v)
    (relB : ∀ {a a'}, relA a a' → B a → B' a' → Prop)
    (f : (a : A) → B a) (f' : (a' : A') → B' a') : Prop :=
  ∀ a a' (r : relA a a'), relB r (f a) (f' a')

/-- The polymorphic identity function. -/
def polyId (A : Type) : A → A := fun x => x

/-- The fiber relation for `A → A` induced by a type equivalence. -/
def polyIdRel (A A' : Type) (h : Nonempty (Equiv A A'))
    (g : A → A) (g' : A' → A') : Prop :=
  ∀ x x', (Classical.choice h).toFun x = x' →
    (Classical.choice h).toFun (g x) = g' x'

/-- Polymorphic identity is certified at `Π A : Type. A → A`. -/
theorem polyIdPiCert :
    PiCert (fun A A' => Nonempty (Equiv A A'))
      (fun A => A → A) (fun A' => A' → A')
      (fun {A A'} h => polyIdRel A A' h)
      polyId polyId := by
  intro A A' h x x' hx
  simpa [polyIdRel, polyId] using hx

end Transport.DependentPi
