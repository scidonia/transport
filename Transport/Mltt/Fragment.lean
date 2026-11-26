import Transport.Mltt.Subst

namespace Transport.Mltt.Fragment

open Transport.Mltt
open Transport.Mltt.Weaken
open Transport.Mltt.Subst

/-- Renaming preserves typing on the simple fragment.  This is the
substitution-algebra core shared with the `Eq` weakening proof, but without
the inductive-family cases. -/
theorem hasType_rename_simple {env : Env} {Γ Δ : Ctx} {ρ : Nat → Nat}
    (hwk : Wk ρ Γ Δ) {t A : Tm} (ht : HasType env Γ t A) (hs : Simple t) :
    HasType env Δ (Tm.rename ρ t) (Tm.rename ρ A) := by
  induction ht generalizing Δ ρ with
  | var Γ x A hx =>
      simp only [Tm.rename]
      exact HasType.var Δ (ρ x) (Tm.rename ρ A) (hwk x A hx)
  | sort Γ i =>
      simp only [Tm.rename]
      exact HasType.sort Δ i
  | pi Γ A B i j hA hB ihA ihB =>
      cases hs with
      | pi hsA hsB =>
          simp only [Tm.rename]
          have hA' : HasType env Δ (Tm.rename ρ A) (Tm.sort i) := by
            simpa [Tm.rename] using ihA (Δ := Δ) (ρ := ρ) hwk hsA
          have hB' : HasType env (Tm.rename ρ A :: Δ)
              (Tm.rename (Tm.upRen ρ) B) (Tm.sort j) := by
            simpa [Tm.rename] using
              ihB (Δ := Tm.rename ρ A :: Δ) (ρ := Tm.upRen ρ) (Wk_extend hwk A) hsB
          exact HasType.pi Δ (Tm.rename ρ A) (Tm.rename (Tm.upRen ρ) B) i j hA' hB'
  | lam Γ A t B i hA ht ihA iht =>
      cases hs with
      | lam hsA hst =>
          simp only [Tm.rename]
          have hA' : HasType env Δ (Tm.rename ρ A) (Tm.sort i) := by
            simpa [Tm.rename] using ihA (Δ := Δ) (ρ := ρ) hwk hsA
          have ht' : HasType env (Tm.rename ρ A :: Δ)
              (Tm.rename (Tm.upRen ρ) t) (Tm.rename (Tm.upRen ρ) B) := by
            simpa [Tm.rename] using
              iht (Δ := Tm.rename ρ A :: Δ) (ρ := Tm.upRen ρ) (Wk_extend hwk A) hst
          exact HasType.lam Δ (Tm.rename ρ A) (Tm.rename (Tm.upRen ρ) t)
            (Tm.rename (Tm.upRen ρ) B) i hA' ht'
  | app Γ t u A B ht hu iht ihu =>
      cases hs with
      | app hst hsu =>
          simp only [Tm.rename]
          have ht' : HasType env Δ (Tm.rename ρ t)
              (Tm.pi (Tm.rename ρ A) (Tm.rename (Tm.upRen ρ) B)) := by
            simpa [Tm.rename] using iht (Δ := Δ) (ρ := ρ) hwk hst
          have hu' : HasType env Δ (Tm.rename ρ u) (Tm.rename ρ A) := by
            simpa [Tm.rename] using ihu (Δ := Δ) (ρ := ρ) hwk hsu
          have h := HasType.app Δ (Tm.rename ρ t) (Tm.rename ρ u)
            (Tm.rename ρ A) (Tm.rename (Tm.upRen ρ) B) ht' hu'
          rw [subst0_eq_substMany] at h
          rw [subst0_eq_substMany, rename_substMany]
          simpa [Tm.upRenN] using h
  | ind Γ I sig args hsig hlen hargs ihargs =>
      cases hs
  | roll Γ I sig c ctor args hsig hctor hlen hparams hctys hrec ihparams ihctys ihrec =>
      cases hs
  | case Γ I n sig scrut C brs i args hsig hn hlen hscrut hmotive hbrs hbranch ihscrut ihmotive ihbranch =>
      cases hs

/-- The context morphism induced by `σ` extends under a binder. -/
theorem subst_cons_morphism {env : Env} {Γ Δ : Ctx} {σ : Nat → Tm}
    (hσ : ∀ x A, ctxLookup Γ x = some A → HasType env Δ (σ x) (Tm.subst σ A))
    (hσs : ∀ x, Simple (σ x)) (A : Tm) :
    ∀ x A', ctxLookup (A :: Γ) x = some A' →
      HasType env (Tm.subst σ A :: Δ) (Tm.upSub σ x) (Tm.subst (Tm.upSub σ) A') := by
  intro x A' hx
  cases x with
  | zero =>
      simp only [ctxLookup, Option.some.injEq] at hx
      subst hx
      have h0 : Tm.upSub σ 0 = Tm.var 0 := rfl
      rw [h0, subst_upSub_shift]
      exact HasType.var _ 0 _ rfl
  | succ y =>
      simp only [ctxLookup] at hx
      cases hl : ctxLookup Γ y with
      | none => simp [hl] at hx
      | some A0 =>
          simp [hl] at hx
          subst hx
          have hbase : HasType env Δ (σ y) (Tm.subst σ A0) := hσ y A0 hl
          have hshift := hasType_rename_simple
            (Wk_insert_front (Tm.subst σ A) Δ) hbase (hσs y)
          have hshift' : HasType env (Tm.subst σ A :: Δ)
              (Tm.shift 1 0 (σ y)) (Tm.shift 1 0 (Tm.subst σ A0)) := by
            simpa [Tm.shift] using hshift
          simpa [Tm.upSub, subst_upSub_shift] using hshift'

/-- General substitution is typing-preserving on the simple fragment. -/
theorem hasType_subst_simple {env : Env} {Γ : Ctx} :
    ∀ {t A : Tm}, HasType env Γ t A → Simple t →
      ∀ {Δ : Ctx} {σ : Nat → Tm},
        (∀ x A, ctxLookup Γ x = some A → HasType env Δ (σ x) (Tm.subst σ A)) →
        (∀ x, Simple (σ x)) →
        HasType env Δ (Tm.subst σ t) (Tm.subst σ A) := by
  intro t A ht
  induction ht with
  | var Γ x A hx =>
      intro hs Δ σ hσ hσs
      simpa [Tm.subst] using hσ x A hx
  | sort Γ i =>
      intro hs Δ σ hσ hσs
      simpa [Tm.subst] using HasType.sort Δ i
  | pi Γ A B i j hA hB ihA ihB =>
      intro hs Δ σ hσ hσs
      cases hs with
      | pi hsA hsB =>
          simp only [Tm.subst]
          have hA' : HasType env Δ (Tm.subst σ A) (Tm.sort i) := by
            simpa [Tm.subst] using ihA hsA (Δ := Δ) (σ := σ) hσ hσs
          have hB' : HasType env (Tm.subst σ A :: Δ)
              (Tm.subst (Tm.upSub σ) B) (Tm.sort j) := by
            simpa [Tm.subst] using
              ihB hsB (Δ := Tm.subst σ A :: Δ) (σ := Tm.upSub σ)
                (subst_cons_morphism hσ hσs A) (Simple.upSub hσs)
          exact HasType.pi Δ (Tm.subst σ A) (Tm.subst (Tm.upSub σ) B) i j hA' hB'
  | lam Γ A t B i hA ht ihA iht =>
      intro hs Δ σ hσ hσs
      cases hs with
      | lam hsA hst =>
          simp only [Tm.subst]
          have hA' : HasType env Δ (Tm.subst σ A) (Tm.sort i) := by
            simpa [Tm.subst] using ihA hsA (Δ := Δ) (σ := σ) hσ hσs
          have ht' : HasType env (Tm.subst σ A :: Δ)
              (Tm.subst (Tm.upSub σ) t) (Tm.subst (Tm.upSub σ) B) :=
            iht hst (Δ := Tm.subst σ A :: Δ) (σ := Tm.upSub σ)
              (subst_cons_morphism hσ hσs A) (Simple.upSub hσs)
          exact HasType.lam Δ (Tm.subst σ A) (Tm.subst (Tm.upSub σ) t)
            (Tm.subst (Tm.upSub σ) B) i hA' ht'
  | app Γ t u A B ht hu iht ihu =>
      intro hs Δ σ hσ hσs
      cases hs with
      | app hst hsu =>
          simp only [Tm.subst]
          have ht' : HasType env Δ (Tm.subst σ t)
              (Tm.pi (Tm.subst σ A) (Tm.subst (Tm.upSub σ) B)) := by
            simpa [Tm.subst] using iht hst (Δ := Δ) (σ := σ) hσ hσs
          have hu' : HasType env Δ (Tm.subst σ u) (Tm.subst σ A) := by
            simpa [Tm.subst] using ihu hsu (Δ := Δ) (σ := σ) hσ hσs
          have h := HasType.app Δ (Tm.subst σ t) (Tm.subst σ u)
            (Tm.subst σ A) (Tm.subst (Tm.upSub σ) B) ht' hu'
          rw [subst_subst0]
          exact h
  | ind Γ I sig args hsig hlen hargs ihargs =>
      intro hs
      cases hs
  | roll Γ I sig c ctor args hsig hctor hlen hparams hctys hrec ihparams ihctys ihrec =>
      intro hs
      cases hs
  | case Γ I n sig scrut C brs i args hsig hn hlen hscrut hmotive hbrs hbranch ihscrut ihmotive ihbranch =>
      intro hs
      cases hs

/-- Single substitution, the form a beta step needs. -/
theorem hasType_subst0_simple {env : Env} {Γ : Ctx} {t A u B : Tm}
    (ht : HasType env (A :: Γ) t B) (hu : HasType env Γ u A)
    (hst : Simple t) (hsu : Simple u) :
    HasType env Γ (Tm.subst0 u t) (Tm.subst0 u B) := by
  have hσ : ∀ x A', ctxLookup (A :: Γ) x = some A' →
      HasType env Γ ((fun
        | 0 => u
        | x + 1 => Tm.var x) x) (Tm.subst (fun
          | 0 => u
          | x + 1 => Tm.var x) A') := by
    intro x A' hx
    cases x with
    | zero =>
        simp only [ctxLookup, Option.some.injEq] at hx
        subst hx
        change HasType env Γ u (Tm.subst (fun
          | 0 => u
          | x + 1 => Tm.var x) (Tm.shift 1 0 A))
        rw [subst_shift]
        change HasType env Γ u (Tm.subst Tm.var A)
        rw [subst_var]
        exact hu
    | succ y =>
        simp only [ctxLookup] at hx
        cases hl : ctxLookup Γ y with
        | none => simp [hl] at hx
        | some A0 =>
            simp [hl] at hx
            subst hx
            change HasType env Γ (Tm.var y) (Tm.subst (fun
              | 0 => u
              | x + 1 => Tm.var x) (Tm.shift 1 0 A0))
            rw [subst_shift]
            change HasType env Γ (Tm.var y) (Tm.subst Tm.var A0)
            rw [subst_var]
            exact HasType.var Γ y A0 hl
  have hσs : ∀ x, Simple ((fun
      | 0 => u
      | x + 1 => Tm.var x) x) := by
    intro x
    cases x with
    | zero => exact hsu
    | succ y => exact Simple.var y
  exact hasType_subst_simple ht hst hσ hσs

end Transport.Mltt.Fragment
