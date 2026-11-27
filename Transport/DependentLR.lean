import Transport.Mltt.Core

/-!
# A closed value logical relation with a dependent Pi clause

The core `Tm` has no reduction relation.  This file starts with the canonical
value fragment: sorts, Pi types, and lambdas.  A Pi certificate is a fiberwise
family of body certificates, not a certificate at one applied result.

Type arguments are closed types.  This keeps substitution in the Pi clause
well behaved without a context relation.
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
  | .ind _ args => args.Forall (ClosedAt k)
  | .roll _ _ args => args.Forall (ClosedAt k)
  | .case _ _ scrut C brs =>
      ClosedAt k scrut ∧ ClosedAt (k + 1) C ∧ brs.Forall (ClosedAt k)

/-- A closed term. -/
def Closed (t : Tm) : Prop := ClosedAt 0 t

/-- Closed type terms. -/
def ClosedTyAt (k : Nat) : Tm → Prop
  | .var i => i < k
  | .sort _ => True
  | .pi A B => ClosedTyAt k A ∧ ClosedTyAt (k + 1) B
  | _ => False

def ClosedTy (t : Tm) : Prop := ClosedTyAt 0 t

theorem ClosedTyAt.mono {k k' : Nat} (h : k ≤ k') {t : Tm} :
    ClosedTyAt k t → ClosedTyAt k' t := by
  induction t generalizing k k' with
  | var i => intro hi; simp [ClosedTyAt] at hi ⊢; omega
  | sort i => intro _; simp [ClosedTyAt]
  | pi A B ihA ihB =>
      intro hc
      simp [ClosedTyAt] at hc ⊢
      exact ⟨ihA h hc.1, ihB (by omega) hc.2⟩
  | lam _ _ _ _ => intro hc; simp [ClosedTyAt] at hc
  | app _ _ _ _ => intro hc; simp [ClosedTyAt] at hc
  | fix _ _ _ _ => intro hc; simp [ClosedTyAt] at hc
  | ind _ _ => intro hc; simp [ClosedTyAt] at hc
  | roll _ _ _ => intro hc; simp [ClosedTyAt] at hc
  | case _ _ _ _ _ => intro hc; simp [ClosedTyAt] at hc

theorem upRen_shiftSub (d c : Nat) :
    Tm.upRen (Tm.shiftSub d c) = Tm.shiftSub d (c + 1) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      simp only [Tm.upRen, Tm.shiftSub]
      by_cases h : i < c
      · simp [h, Nat.succ_lt_succ h]
      · have hc : ¬ i + 1 < c + 1 := by omega
        simp [h, hc]
        omega

theorem closedTy_shift (d c : Nat) (t : Tm) (h : ClosedTyAt c t) :
    Tm.shift d c t = t := by
  induction t generalizing c with
  | var i =>
      simp [ClosedTyAt] at h
      simp [Tm.shift, Tm.rename, Tm.shiftSub, h]
  | sort i => simp [Tm.shift, Tm.rename]
  | pi A B ihA ihB =>
      simp [ClosedTyAt] at h
      have hA := ihA c h.1
      have hB := ihB (c + 1) h.2
      simp [Tm.shift, Tm.rename, upRen_shiftSub, hA, hB]
  | lam _ _ _ _ => simp [ClosedTyAt] at h
  | app _ _ _ _ => simp [ClosedTyAt] at h
  | fix _ _ _ _ => simp [ClosedTyAt] at h
  | ind _ _ => simp [ClosedTyAt] at h
  | roll _ _ _ => simp [ClosedTyAt] at h
  | case _ _ _ _ _ => simp [ClosedTyAt] at h

theorem subst_closedTy (σ : Nat → Tm) {k : Nat}
    (hσ : ∀ i, i < k → σ i = .var i)
    (t : Tm) (h : ClosedTyAt k t) : Tm.subst σ t = t := by
  induction t generalizing k with
  | var i =>
      simp [ClosedTyAt] at h
      simp [Tm.subst, hσ i h]
  | sort i => simp [Tm.subst]
  | pi A B ihA ihB =>
      simp [ClosedTyAt] at h
      have hA := ihA hσ h.1
      have hσ' : ∀ i, i < k + 1 → Tm.upSub σ i = .var i := by
        intro i hi
        cases i with
        | zero => rfl
        | succ i =>
            have hi' : i < k := by omega
            simp [Tm.upSub, hσ i hi', Tm.shift, Tm.rename, Tm.shiftSub]
      have hB := ihB hσ' h.2
      simp [Tm.subst, hA, hB]
  | lam _ _ _ _ => simp [ClosedTyAt] at h
  | app _ _ _ _ => simp [ClosedTyAt] at h
  | fix _ _ _ _ => simp [ClosedTyAt] at h
  | ind _ _ => simp [ClosedTyAt] at h
  | roll _ _ _ => simp [ClosedTyAt] at h
  | case _ _ _ _ _ => simp [ClosedTyAt] at h

theorem subst0_closedTy (x t : Tm) (h : ClosedTy t) :
    Tm.subst0 x t = t := by
  unfold Tm.subst0
  apply subst_closedTy (σ := fun
    | 0 => x
    | i + 1 => .var i) (k := 0)
  · intro i hi; omega
  · exact h

theorem subst0_var0 (x : Tm) : Tm.subst0 x (.var 0) = x := by
  simp [Tm.subst0, Tm.subst]

theorem subst0_pi_body (x : Tm) :
    Tm.subst0 x (.pi (.var 0) (.var 1)) = .pi x (Tm.shift 1 0 x) := by
  simp [Tm.subst0, Tm.subst, Tm.upSub, Tm.shift, Tm.rename, Tm.shiftSub]

theorem subst0_lam_poly (x : Tm) :
    Tm.subst0 x (.lam (.var 0) (.var 0)) = .lam x (.var 0) := by
  simp [Tm.subst0, Tm.subst, Tm.upSub]

/-- The value/type logical relation. `true` is the type relation, `false` the
term relation. -/
inductive LR : Bool → Tm → Tm → Tm → Tm → Prop
  | tySort (i : Nat) :
      LR true (.sort i) (.sort i) (.sort i) (.sort i)
  | tyPi {A A' B B' : Tm} :
      ClosedTy (.pi A B) →
      ClosedTy (.pi A' B') →
      LR true A A' A A' →
      (∀ x x', Closed x → Closed x' →
        LR false A A' x x' →
        LR true (Tm.subst0 x B) (Tm.subst0 x' B')
          (Tm.subst0 x B) (Tm.subst0 x' B')) →
      LR true (.pi A B) (.pi A' B') (.pi A B) (.pi A' B')
  | tmSort {A A' : Tm} (i : Nat) :
      ClosedTy A →
      LR true A A' A A' →
      LR false (.sort i) (.sort i) A A'
  | tmPi {A A' B B' t t' : Tm} :
      ClosedTy (.pi A B) →
      ClosedTy (.pi A' B') →
      LR true (.pi A B) (.pi A' B') (.pi A B) (.pi A' B') →
      (∀ x x', Closed x → Closed x' →
        LR false A A' x x' →
        LR false (Tm.subst0 x B) (Tm.subst0 x' B')
          (Tm.subst0 x t) (Tm.subst0 x' t')) →
      LR false (.pi A B) (.pi A' B') (.lam A t) (.lam A' t')

def TyRel (A A' : Tm) : Prop := LR true A A' A A'
def TmRel (A A' t t' : Tm) : Prop := LR false A A' t t'

def polyIdTy : Tm := .pi (.sort 0) (.pi (.var 0) (.var 1))
def polyIdTm : Tm := .lam (.sort 0) (.lam (.var 0) (.var 0))


theorem closedTy_polyIdTy : ClosedTy polyIdTy := by
  simp [polyIdTy, ClosedTy, ClosedTyAt]

theorem closedTy_pi_self {A : Tm} (h : ClosedTy A) : ClosedTy (.pi A A) := by
  exact ⟨h, ClosedTyAt.mono (by omega) h⟩

theorem tyRel_polyIdTy : TyRel polyIdTy polyIdTy := by
  unfold TyRel polyIdTy
  apply LR.tyPi
  · exact closedTy_polyIdTy
  · exact closedTy_polyIdTy
  · exact LR.tySort 0
  · intro A A' hA hA' hrel
    cases hrel with
    | tmSort hclosedA hAty =>
        rw [subst0_pi_body]
        rw [closedTy_shift 1 0 A hclosedA, closedTy_shift 1 0 A' hclosedA']
        apply LR.tyPi
        · exact closedTy_pi_self hclosedA
        · exact closedTy_pi_self hclosedA'
        · exact hAty
        · intro x x' hx hx' hrelx
          have hclosedShiftA : ClosedTy (Tm.shift 1 0 A) := by
            rw [closedTy_shift 1 0 A hclosedA]
            exact hclosedA
          rw [subst0_closedTy x (Tm.shift 1 0 A) hclosedShiftA]
          rw [closedTy_shift 1 0 A hclosedA, closedTy_shift 1 0 A' hclosedA']
          exact hAty

theorem tmRel_polyIdTm : TmRel polyIdTy polyIdTy polyIdTm polyIdTm := by
  unfold TmRel polyIdTy polyIdTm
  apply LR.tmPi
  · exact closedTy_polyIdTy
  · exact closedTy_polyIdTy
  · exact tyRel_polyIdTy
  · intro A A' hA hA' hrel
    cases hrel with
    | tmSort hclosedA hAty =>
        rw [subst0_lam_poly, subst0_pi_body]
        rw [closedTy_shift 1 0 A hclosedA, closedTy_shift 1 0 A' hclosedA']
        apply LR.tmPi
        · exact closedTy_pi_self hclosedA
        · exact closedTy_pi_self hclosedA'
        · apply LR.tyPi
          · exact closedTy_pi_self hclosedA
          · exact closedTy_pi_self hclosedA'
          · exact hAty
          · intro x x' hx hx' hrelx
            have hclosedShiftA : ClosedTy (Tm.shift 1 0 A) := by
              rw [closedTy_shift 1 0 A hclosedA]
              exact hclosedA
            rw [subst0_closedTy x (Tm.shift 1 0 A) hclosedShiftA]
            rw [closedTy_shift 1 0 A hclosedA, closedTy_shift 1 0 A' hclosedA']
            exact hAty
        · intro x x' hx hx' hrelx
          simpa [subst0_var0] using hrelx

end Transport.DependentLR
