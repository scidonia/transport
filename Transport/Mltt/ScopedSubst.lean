import Transport.Mltt.Scoped
import Transport.Mltt.Subst

/-!
# Scoped substitution

The first prerequisite for full-core substitution: well-scoped terms are closed
under renaming and substitution, and a context morphism is typed pointwise.

This file does not yet strengthen `HasType` with a well-formedness invariant.
It establishes the scoping layer that the typing proof will consume.
-/

namespace Transport.Mltt.Scoped

open Transport.Mltt
open Transport.Mltt.Weaken

theorem upRenN_lt {m : Nat} {f : Nat → Nat} {d d' : Nat}
    (hf : ∀ x, x < d → f x < d') :
    ∀ x, x < d + m → Tm.upRenN m f x < d' + m := by
  induction m with
  | zero => simpa [Tm.upRenN] using hf
  | succ m ih =>
      intro x hx
      rw [Tm.upRenN]
      cases x with
      | zero => simp [Tm.upRen]; omega
      | succ x =>
          have hx' : x < d + m := by omega
          simp only [Tm.upRen]
          have := ih x hx'
          omega

private theorem WellScoped.rename_aux :
    ∀ (t : Tm) (f : Nat → Nat) (d d' : Nat), (∀ x, x < d → f x < d') →
      WellScoped d t → WellScoped d' (Tm.rename f t) := by
  apply tm_strong_induction
  intro t ih f d d' hf h
  cases t with
  | var x =>
      cases h with
      | var hx => simp [Tm.rename]; exact WellScoped.var (hf x hx)
  | sort i => simp [Tm.rename]; exact WellScoped.sort
  | pi A B =>
      cases h with
      | pi hA hB =>
          simp only [Tm.rename]
          apply WellScoped.pi
          · exact ih A (size_lt_pi_left A B) f d d' hf hA
          · exact ih B (size_lt_pi_right A B) (Tm.upRen f) (d + 1) (d' + 1)
              (upRenN_lt (m := 1) hf) hB
  | lam A b =>
      cases h with
      | lam hA hb =>
          simp only [Tm.rename]
          apply WellScoped.lam
          · exact ih A (size_lt_lam_left A b) f d d' hf hA
          · exact ih b (size_lt_lam_right A b) (Tm.upRen f) (d + 1) (d' + 1)
              (upRenN_lt (m := 1) hf) hb
  | app g u =>
      cases h with
      | app hf' hu =>
          simp only [Tm.rename]
          exact WellScoped.app
            (ih g (size_lt_app_left g u) f d d' hf hf')
            (ih u (size_lt_app_right g u) f d d' hf hu)
  | fix A b =>
      cases h with
      | fix hA hb =>
          simp only [Tm.rename]
          apply WellScoped.fix
          · exact ih A (size_lt_fix_left A b) f d d' hf hA
          · exact ih b (size_lt_fix_right A b) (Tm.upRen f) (d + 1) (d' + 1)
              (upRenN_lt (m := 1) hf) hb
  | ind I args =>
      cases h with
      | ind hargs =>
          simp only [Tm.rename]
          apply WellScoped.ind
          intro a ha
          rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
          exact ih b (size_lt_ind_mem hb) f d d' hf (hargs b hb)
  | roll I c args =>
      cases h with
      | roll hargs =>
          simp only [Tm.rename]
          apply WellScoped.roll
          intro a ha
          rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
          exact ih b (size_lt_roll_mem hb) f d d' hf (hargs b hb)
  | case I n scrut C brs =>
      cases h with
      | case hscrut hC hbrs =>
          simp only [Tm.rename]
          apply WellScoped.case
          · exact ih scrut (size_lt_case_scrut I n scrut C brs) f d d' hf hscrut
          · exact ih C (size_lt_case_motive I n scrut C brs) (Tm.upRenN (n + 1) f) (d + n + 1) (d' + n + 1)
              (by simpa [Nat.add_assoc] using upRenN_lt (m := n + 1) hf) hC
          · intro b hb
            rcases List.mem_map.mp hb with ⟨c, hc, rfl⟩
            exact ih c (size_lt_case_mem hc) f d d' hf (hbrs c hc)

theorem WellScoped.rename (f : Nat → Nat) {d d' : Nat} {t : Tm}
    (hf : ∀ x, x < d → f x < d') (h : WellScoped d t) :
    WellScoped d' (Tm.rename f t) :=
  WellScoped.rename_aux t f d d' hf h

theorem WellScoped.shift {d : Nat} {t : Tm} (h : WellScoped d t) :
    WellScoped (d + 1) (Tm.shift 1 0 t) := by
  simpa [Tm.shift] using h.rename (Tm.shiftSub 1 0) (fun x hx => by
    simp [Tm.shiftSub, hx])

theorem upSubN_wellScoped (m : Nat) {σ : Nat → Tm} {d d' : Nat}
    (hσ : ∀ x, x < d → WellScoped d' (σ x)) :
    ∀ x, x < d + m → WellScoped (d' + m) (Tm.upSubN m σ x) := by
  induction m with
  | zero => simpa [Tm.upSubN] using hσ
  | succ m ih =>
      intro x hx
      rw [Tm.upSubN]
      cases x with
      | zero => exact WellScoped.var (by omega)
      | succ x =>
          have hx' : x < d + m := by omega
          have h := ih x hx'
          simpa [Tm.upSub, Nat.add_assoc] using h.shift

private theorem wellScoped_subst_aux :
    ∀ (t : Tm) (d d' : Nat) (σ : Nat → Tm),
      WellScoped d t → (∀ x, x < d → WellScoped d' (σ x)) →
      WellScoped d' (Tm.subst σ t) := by
  apply tm_strong_induction
  intro t ih d d' σ ht hσ
  cases t with
  | var x =>
      cases ht with
      | var hx => simpa [Tm.subst] using hσ x hx
  | sort i => simpa [Tm.subst] using WellScoped.sort
  | pi A B =>
      cases ht with
      | pi hA hB =>
          simpa [Tm.subst] using WellScoped.pi
            (ih A (size_lt_pi_left A B) d d' σ hA hσ)
            (ih B (size_lt_pi_right A B) (d + 1) (d' + 1) (Tm.upSub σ)
              hB (by simpa [Tm.upSubN, Tm.upSub] using upSubN_wellScoped 1 hσ))
  | lam A b =>
      cases ht with
      | lam hA hb =>
          simpa [Tm.subst] using WellScoped.lam
            (ih A (size_lt_lam_left A b) d d' σ hA hσ)
            (ih b (size_lt_lam_right A b) (d + 1) (d' + 1) (Tm.upSub σ)
              hb (by simpa [Tm.upSubN, Tm.upSub] using upSubN_wellScoped 1 hσ))
  | app f u =>
      cases ht with
      | app hf hu =>
          simpa [Tm.subst] using WellScoped.app
            (ih f (size_lt_app_left f u) d d' σ hf hσ)
            (ih u (size_lt_app_right f u) d d' σ hu hσ)
  | fix A b =>
      cases ht with
      | fix hA hb =>
          simpa [Tm.subst] using WellScoped.fix
            (ih A (size_lt_fix_left A b) d d' σ hA hσ)
            (ih b (size_lt_fix_right A b) (d + 1) (d' + 1) (Tm.upSub σ)
              hb (by simpa [Tm.upSubN, Tm.upSub] using upSubN_wellScoped 1 hσ))
  | ind I args =>
      cases ht with
      | ind hargs =>
          simp only [Tm.subst]
          apply WellScoped.ind
          intro a ha
          rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
          exact ih b (size_lt_ind_mem hb) d d' σ (hargs b hb) hσ
  | roll I c args =>
      cases ht with
      | roll hargs =>
          simp only [Tm.subst]
          apply WellScoped.roll
          intro a ha
          rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
          exact ih b (size_lt_roll_mem hb) d d' σ (hargs b hb) hσ
  | case I n scrut C brs =>
      cases ht with
      | case hscrut hC hbrs =>
          simp only [Tm.subst]
          apply WellScoped.case
          · exact ih scrut (size_lt_case_scrut I n scrut C brs) d d' σ hscrut hσ
          · exact ih C (size_lt_case_motive I n scrut C brs) (d + n + 1) (d' + n + 1)
              (Tm.upSubN (n + 1) σ) hC
              (by simpa [Tm.upSubN, Nat.add_assoc] using upSubN_wellScoped (n + 1) hσ)
          · intro b hb
            rcases List.mem_map.mp hb with ⟨c, hc, rfl⟩
            exact ih c (size_lt_case_mem hc) d d' σ (hbrs c hc) hσ

theorem wellScoped_subst {d d' : Nat} {σ : Nat → Tm} {t : Tm}
    (ht : WellScoped d t)
    (hσ : ∀ x, x < d → WellScoped d' (σ x)) :
    WellScoped d' (Tm.subst σ t) :=
  wellScoped_subst_aux t d d' σ ht hσ

def CtxMap (env : Env) (σ : Nat → Tm) (Γ Δ : Ctx) : Prop :=
  ∀ x A, ctxLookup Γ x = some A → HasType env Δ (σ x) (Tm.subst σ A)


/-- Lifted substitutions agree on the scoped part. -/
theorem upSubN_eq_of_lt (m : Nat) {d : Nat} {τ τ' : Nat → Tm}
    (h : ∀ x, x < d → τ x = τ' x) :
    ∀ x, x < d + m → Tm.upSubN m τ x = Tm.upSubN m τ' x := by
  induction m with
  | zero => simpa [Tm.upSubN] using h
  | succ m ih =>
      intro x hx
      rw [Tm.upSubN, Tm.upSubN]
      cases x with
      | zero => rfl
      | succ x =>
          have hx' : x < d + m := by omega
          have hh := ih x hx'
          simp [Tm.upSub, hh]

private theorem subst_congr_aux :
    ∀ (t : Tm) (d : Nat) (τ τ' : Nat → Tm),
      WellScoped d t → (∀ x, x < d → τ x = τ' x) →
      Tm.subst τ t = Tm.subst τ' t := by
  apply tm_strong_induction
  intro t ih d τ τ' h heq
  cases t with
  | var x =>
      cases h with
      | var hx => simpa [Tm.subst] using heq x hx
  | sort i => simp [Tm.subst]
  | pi A B =>
      cases h with
      | pi hA hB =>
          simp only [Tm.subst]
          rw [ih A (size_lt_pi_left A B) d τ τ' hA heq]
          rw [ih B (size_lt_pi_right A B) (d + 1) (Tm.upSub τ) (Tm.upSub τ') hB
            (by
              intro x hx
              cases x with
              | zero => rfl
              | succ x =>
                  have hx' : x < d := by omega
                  simp [Tm.upSub, heq x hx'])]
  | lam A b =>
      cases h with
      | lam hA hb =>
          simp only [Tm.subst]
          rw [ih A (size_lt_lam_left A b) d τ τ' hA heq]
          rw [ih b (size_lt_lam_right A b) (d + 1) (Tm.upSub τ) (Tm.upSub τ') hb
            (by
              intro x hx
              cases x with
              | zero => rfl
              | succ x =>
                  have hx' : x < d := by omega
                  simp [Tm.upSub, heq x hx'])]
  | app f u =>
      cases h with
      | app hf hu =>
          simp only [Tm.subst]
          rw [ih f (size_lt_app_left f u) d τ τ' hf heq]
          rw [ih u (size_lt_app_right f u) d τ τ' hu heq]
  | fix A b =>
      cases h with
      | fix hA hb =>
          simp only [Tm.subst]
          rw [ih A (size_lt_fix_left A b) d τ τ' hA heq]
          rw [ih b (size_lt_fix_right A b) (d + 1) (Tm.upSub τ) (Tm.upSub τ') hb
            (by
              intro x hx
              cases x with
              | zero => rfl
              | succ x =>
                  have hx' : x < d := by omega
                  simp [Tm.upSub, heq x hx'])]
  | ind I args =>
      cases h with
      | ind hargs =>
          simp only [Tm.subst]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact ih a (size_lt_ind_mem ha) d τ τ' (hargs a ha) heq
  | roll I c args =>
      cases h with
      | roll hargs =>
          simp only [Tm.subst]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact ih a (size_lt_roll_mem ha) d τ τ' (hargs a ha) heq
  | case I n scrut C brs =>
      cases h with
      | case hscrut hC hbrs =>
          simp only [Tm.subst]
          rw [ih scrut (size_lt_case_scrut I n scrut C brs) d τ τ' hscrut heq]
          rw [ih C (size_lt_case_motive I n scrut C brs) (d + n + 1)
            (Tm.upSubN (n + 1) τ) (Tm.upSubN (n + 1) τ') hC
            (upSubN_eq_of_lt (n + 1) heq)]
          congr 1
          apply List.map_congr_left
          intro b hb
          exact ih b (size_lt_case_mem hb) d τ τ' (hbrs b hb) heq

/-- Substitution is determined by its values on the free variables below the
scope. -/
theorem subst_congr_of_wellScoped {d : Nat} {τ τ' : Nat → Tm} {t : Tm}
    (h : WellScoped d t) (heq : ∀ x, x < d → τ x = τ' x) :
    Tm.subst τ t = Tm.subst τ' t :=
  subst_congr_aux t d τ τ' h heq

/-- Substituting arguments and then a substitution equals substituting the
mapped arguments, when the term is scoped by the argument list. -/
theorem substMany_subst_of_wellScoped (σ : Nat → Tm) (args : List Tm) (t : Tm)
    (h : WellScoped args.length t) :
    substMany (args.map (Tm.subst σ)) t = Tm.subst σ (substMany args t) := by
  rw [substMany_eq_subst, substMany_eq_subst, Subst.subst_subst]
  apply subst_congr_of_wellScoped (d := args.length)
    (τ := substFun (args.map (Tm.subst σ)))
    (τ' := fun x => Tm.subst σ (substFun args x)) h
  intro x hx
  simp [substFun, hx]

end Transport.Mltt.Scoped
