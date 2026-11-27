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


/-- A type-valued Pi certificate at a fibered action: a dependent family of
fiber derivations over the index relation. -/
def FiberPiCert (F : FiberRel)
    (indexRel : F.Index → F.Index → Prop)
    (P : (i : F.Index) → Process (F.Source i))
    (Q : (i : F.Index) → Process (F.Residual i))
    (measure : (i : F.Index) → (Q i).Config → Nat)
    (f : (i : F.Index) → (P i).Config)
    (f' : (i : F.Index) → (Q i).Config) : Type (u + 1) :=
  ∀ i i' (_ : indexRel i i'),
    FiberDerivation F P Q measure i i' (f i) (f' i')

/-- Soundness of a fibered Pi certificate: every fiber is bisimilar. -/
theorem FiberPiCert.sound (F : FiberRel)
    (indexRel : F.Index → F.Index → Prop)
    (P : (i : F.Index) → Process (F.Source i))
    (Q : (i : F.Index) → Process (F.Residual i))
    (measure : (i : F.Index) → (Q i).Config → Nat)
    (f : (i : F.Index) → (P i).Config)
    (f' : (i : F.Index) → (Q i).Config)
    (h : FiberPiCert F indexRel P Q measure f f') :
    ∀ i i' (_ : indexRel i i') n, FiberBisim F P Q i i' n (f i) (f' i') := by
  intro i i' hi n
  exact FiberDerivation.sound F P Q measure i i' (f i) (f' i') (h i i' hi) n

/-- A fold step at one fiber. -/
def FiberDerivation.fold (F : FiberRel)
    (P : (i : F.Index) → Process (F.Source i))
    (Q : (i : F.Index) → Process (F.Residual i))
    (measure : (i : F.Index) → (Q i).Config → Nat)
    (i i' : F.Index) (p : (P i).Config) (q : (Q i').Config)
    (cert : FiberFoldCert F P Q measure i i' p q)
    (rest : FiberDerivation F P Q measure i i' cert.p' cert.q') :
    FiberDerivation F P Q measure i i' p q :=
  DerivationRel.fold p q cert rest

/-- A generalisation step at one fiber. -/
def FiberDerivation.generalise (F : FiberRel)
    (P : (i : F.Index) → Process (F.Source i))
    (Q : (i : F.Index) → Process (F.Residual i))
    (measure : (i : F.Index) → (Q i).Config → Nat)
    (i i' : F.Index) (p : (P i).Config) {Params : Type u}
    (g : FiberGenCert F P Q i i' Params) (σ : Params)
    (hsource : g.source σ = p)
    (rest : FiberDerivation F P Q measure i i' p (g.schema σ)) :
    FiberDerivation F P Q measure i i' p (g.schema σ) :=
  DerivationRel.generalise p g σ hsource rest

/-- A halted process with no observation. -/
def haltNat : Process Nat where
  Config := Unit
  step := fun _ => none
  obs := fun _ => none

theorem bisimHalt (n : Nat) :
    BisimRel (fun _ _ => True) haltNat haltNat n () () := by
  cases n with
  | zero => trivial
  | succ n => simp [BisimRel, haltNat]

/-- The trivial one-point fiber. -/
def trivialFiber : FiberRel where
  Index := Unit
  Source := fun _ => Nat
  Residual := fun _ => Nat
  rel := fun _ _ _ _ => True

def trivialP (i : trivialFiber.Index) : Process (trivialFiber.Source i) := haltNat
def trivialQ (i : trivialFiber.Index) : Process (trivialFiber.Residual i) := haltNat
def trivialMeasure (i : trivialFiber.Index) : (trivialQ i).Config → Nat := fun _ => 0

/-- The concrete fibered Pi certificate for the identity family on the trivial
fiber. -/
def trivialPi :
    FiberPiCert trivialFiber (fun _ _ => True) trivialP trivialQ trivialMeasure
      (fun _ => ()) (fun _ => ()) := by
  intro i i' _
  cases i
  cases i'
  exact DerivationRel.cert (rel := fun _ _ => True)
    (P := trivialP ()) (Q := trivialQ ())
    (measure := trivialMeasure ()) () ()
    (by
      change ∀ n, BisimRel (fun _ _ => True) haltNat haltNat n () ()
      exact bisimHalt)

example : ∀ n, FiberBisim trivialFiber trivialP trivialQ () () n () () :=
  FiberPiCert.sound trivialFiber (fun _ _ => True) trivialP trivialQ trivialMeasure
    (fun _ => ()) (fun _ => ()) trivialPi () () trivial


/-- A countdown process: steps `n+1` to `n`, halts and observes at zero. -/
abbrev countdown : Process Unit where
  Config := Nat
  step := fun n => if n = 0 then none else some (n - 1)
  obs := fun n => if n = 0 then some () else none

theorem bisimCountdown (m n : Nat) :
    BisimRel (fun _ _ => True) countdown countdown m n n := by
  induction m generalizing n with
  | zero => trivial
  | succ m ih =>
      cases n with
      | zero => simp [BisimRel]
      | succ n =>
          simp [BisimRel]
          exact ih n

/-- The countdown fiber, indexed by the starting number. -/
abbrev countdownFiber : FiberRel where
  Index := Nat
  Source := fun _ => Unit
  Residual := fun _ => Unit
  rel := fun _ _ _ _ => True

abbrev countdownP (i : countdownFiber.Index) : Process (countdownFiber.Source i) := countdown
abbrev countdownQ (i : countdownFiber.Index) : Process (countdownFiber.Residual i) := countdown
abbrev countdownMeasure (i : countdownFiber.Index) : (countdownQ i).Config → Nat := fun n => n

/-- A fold derivation at every countdown start. -/
def countdownDeriv :
    (n : Nat) → FiberDerivation countdownFiber countdownP countdownQ countdownMeasure n n n n
  | 0 => by
      exact DerivationRel.halt (0 : countdownP 0 |>.Config) (0 : countdownQ 0 |>.Config)
        (by simp) (by simp)
        (by simpa [countdownFiber, countdownP, countdownQ, countdown] using bisimCountdown 1 0)
  | n + 1 => by
      exact DerivationRel.fold (p := n + 1) (q := n + 1)
        (cert :=
          { p' := n
            q' := n
            step_p := by simp
            step_q := by simp
            bisim := by
              intro m
              simpa [countdownFiber, countdownP, countdownQ] using bisimCountdown m (n + 1)
            guarded := by simp [countdownMeasure] })
        (rest := countdownDeriv n)

/-- The countdown fibered Pi certificate: a dependent family of fold
derivations over equality of starting indices. -/
def countdownPi :
    FiberPiCert countdownFiber (fun i i' => i = i')
      countdownP countdownQ countdownMeasure (fun n => n) (fun n => n) := by
  intro n n' h
  subst h
  exact countdownDeriv n

end Transport.FiberAction
