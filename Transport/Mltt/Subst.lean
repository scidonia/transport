import Transport.Mltt.Weaken

namespace Transport.Mltt.Subst

open Transport.Mltt
open Transport.Mltt.Weaken

/-! ## Renaming and substitution algebra -/

theorem upRen_id : Tm.upRen id = id := by
  funext x
  cases x with
  | zero => rfl
  | succ y => rfl

theorem upRenN_id : ∀ n, Tm.upRenN n id = id
  | 0 => rfl
  | n + 1 => by
      rw [Tm.upRenN, upRenN_id n, upRen_id]

theorem map_rename_id (l : List Tm) (h : ∀ a ∈ l, Tm.rename id a = a) :
    List.map (Tm.rename id) l = l := by
  calc
    List.map (Tm.rename id) l = List.map id l := by
      apply List.map_congr_left
      exact h
    _ = l := List.map_id l

theorem map_subst_var (l : List Tm) (h : ∀ a ∈ l, Tm.subst Tm.var a = a) :
    List.map (Tm.subst Tm.var) l = l := by
  calc
    List.map (Tm.subst Tm.var) l = List.map id l := by
      apply List.map_congr_left
      exact h
    _ = l := List.map_id l

theorem rename_id (t : Tm) : Tm.rename id t = t := by
  revert t
  apply tm_strong_induction
  intro t ih
  cases t with
  | var x => simp [Tm.rename]
  | sort i => simp [Tm.rename]
  | pi A B =>
      simp only [Tm.rename]
      rw [upRen_id, ih A (size_lt_pi_left A B), ih B (size_lt_pi_right A B)]
  | lam A B =>
      simp only [Tm.rename]
      rw [upRen_id, ih A (size_lt_lam_left A B), ih B (size_lt_lam_right A B)]
  | app A B =>
      simp only [Tm.rename]
      rw [ih A (size_lt_app_left A B), ih B (size_lt_app_right A B)]
  | fix A B =>
      simp only [Tm.rename]
      rw [upRen_id, ih A (size_lt_fix_left A B), ih B (size_lt_fix_right A B)]
  | ind I args =>
      simp only [Tm.rename]
      congr 1
      exact map_rename_id args (fun a ha => ih a (size_lt_ind_mem ha))
  | roll I c args =>
      simp only [Tm.rename]
      congr 1
      exact map_rename_id args (fun a ha => ih a (size_lt_roll_mem ha))
  | case I n scrut C brs =>
      simp only [Tm.rename]
      rw [upRenN_id (n + 1), ih scrut (size_lt_case_scrut I n scrut C brs),
          ih C (size_lt_case_motive I n scrut C brs)]
      congr 1
      exact map_rename_id brs (fun a ha => ih a (size_lt_case_mem ha))

theorem shift_eq_rename (d c : Nat) (t : Tm) :
    Tm.shift d c t = Tm.rename (Tm.shiftSub d c) t := rfl

theorem subst_shift (τ : Nat → Tm) (A : Tm) :
    Tm.subst τ (Tm.shift 1 0 A) = Tm.subst (fun x => τ (x + 1)) A := by
  rw [Tm.shift, subst_rename]
  simp [Tm.shiftSub]

theorem subst_upSub_shift (σ : Nat → Tm) (A : Tm) :
    Tm.subst (Tm.upSub σ) (Tm.shift 1 0 A)
      = Tm.shift 1 0 (Tm.subst σ A) := by
  rw [Tm.shift, Tm.shift, subst_rename, rename_subst]
  congr 1

theorem upSub_var : Tm.upSub Tm.var = Tm.var := by
  funext x
  cases x with
  | zero => rfl
  | succ y =>
      simp [Tm.upSub, Tm.shift, Tm.rename, Tm.shiftSub]

theorem upSubN_var : ∀ n, Tm.upSubN n Tm.var = Tm.var
  | 0 => rfl
  | n + 1 => by
      rw [Tm.upSubN, upSubN_var n, upSub_var]

theorem subst_var (t : Tm) : Tm.subst Tm.var t = t := by
  revert t
  apply tm_strong_induction
  intro t ih
  cases t with
  | var x => simp [Tm.subst]
  | sort i => simp [Tm.subst]
  | pi A B =>
      simp only [Tm.subst]
      rw [ih A (size_lt_pi_left A B), upSub_var, ih B (size_lt_pi_right A B)]
  | lam A B =>
      simp only [Tm.subst]
      rw [ih A (size_lt_lam_left A B), upSub_var, ih B (size_lt_lam_right A B)]
  | app A B =>
      simp only [Tm.subst]
      rw [ih A (size_lt_app_left A B), ih B (size_lt_app_right A B)]
  | fix A B =>
      simp only [Tm.subst]
      rw [ih A (size_lt_fix_left A B), upSub_var, ih B (size_lt_fix_right A B)]
  | ind I args =>
      simp only [Tm.subst]
      congr 1
      exact map_subst_var args (fun a ha => ih a (size_lt_ind_mem ha))
  | roll I c args =>
      simp only [Tm.subst]
      congr 1
      exact map_subst_var args (fun a ha => ih a (size_lt_roll_mem ha))
  | case I n scrut C brs =>
      simp only [Tm.subst]
      rw [ih scrut (size_lt_case_scrut I n scrut C brs), upSubN_var (n + 1),
          ih C (size_lt_case_motive I n scrut C brs)]
      congr 1
      exact map_subst_var brs (fun a ha => ih a (size_lt_case_mem ha))

theorem upSub_comp (σ τ : Nat → Tm) :
    Tm.upSub (fun x => Tm.subst σ (τ x))
      = fun x => Tm.subst (Tm.upSub σ) (Tm.upSub τ x) := by
  funext x
  cases x with
  | zero => simp [Tm.upSub, Tm.subst]
  | succ y =>
      simp only [Tm.upSub]
      rw [subst_upSub_shift]

theorem upSubN_comp (m : Nat) (σ τ : Nat → Tm) :
    Tm.upSubN m (fun x => Tm.subst σ (τ x))
      = fun x => Tm.subst (Tm.upSubN m σ) (Tm.upSubN m τ x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Tm.upSubN, Tm.upSubN, Tm.upSubN]
      rw [ih]
      exact upSub_comp _ _

theorem subst_subst (σ τ : Nat → Tm) (t : Tm) :
    Tm.subst σ (Tm.subst τ t) = Tm.subst (fun x => Tm.subst σ (τ x)) t := by
  revert σ τ
  refine tm_strong_induction
    (P := fun t => ∀ σ τ : Nat → Tm,
      Tm.subst σ (Tm.subst τ t) = Tm.subst (fun x => Tm.subst σ (τ x)) t) ?_ t
  intro t ih σ τ
  cases t with
  | var x => simp [Tm.subst]
  | sort i => simp [Tm.subst]
  | pi A B =>
      simp only [Tm.subst]
      rw [ih A (size_lt_pi_left A B) σ τ,
          ih B (size_lt_pi_right A B) (Tm.upSub σ) (Tm.upSub τ), upSub_comp]
  | lam A B =>
      simp only [Tm.subst]
      rw [ih A (size_lt_lam_left A B) σ τ,
          ih B (size_lt_lam_right A B) (Tm.upSub σ) (Tm.upSub τ), upSub_comp]
  | app A B =>
      simp only [Tm.subst]
      rw [ih A (size_lt_app_left A B) σ τ, ih B (size_lt_app_right A B) σ τ]
  | fix A B =>
      simp only [Tm.subst]
      rw [ih A (size_lt_fix_left A B) σ τ,
          ih B (size_lt_fix_right A B) (Tm.upSub σ) (Tm.upSub τ), upSub_comp]
  | ind I args =>
      simp only [Tm.subst]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact ih a (size_lt_ind_mem ha) σ τ
  | roll I c args =>
      simp only [Tm.subst]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact ih a (size_lt_roll_mem ha) σ τ
  | case I n scrut C brs =>
      simp only [Tm.subst]
      rw [ih scrut (size_lt_case_scrut I n scrut C brs) σ τ,
          ih C (size_lt_case_motive I n scrut C brs) (Tm.upSubN (n + 1) σ) (Tm.upSubN (n + 1) τ),
          upSubN_comp]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact ih a (size_lt_case_mem ha) σ τ

theorem subst0_fun_comp (σ : Nat → Tm) (u : Tm) :
    (fun x => Tm.subst σ ((fun
        | 0 => u
        | x + 1 => Tm.var x) x))
      = (fun x => Tm.subst ((fun
        | 0 => Tm.subst σ u
        | x + 1 => Tm.var x)) (Tm.upSub σ x)) := by
  funext x
  cases x with
  | zero => simp [Tm.upSub, Tm.subst]
  | succ y =>
      simp only [Tm.upSub, Tm.subst]
      rw [subst_shift]
      have h : (fun x => (fun
          | 0 => Tm.subst σ u
          | x + 1 => Tm.var x) (x + 1)) = Tm.var := by
        funext z
        rfl
      rw [h, subst_var]

/-- Substituting a term for variable 0 commutes with a preceding substitution
in the expected way: the outer substitution reaches the argument. -/
theorem subst_subst0 (σ : Nat → Tm) (u B : Tm) :
    Tm.subst σ (Tm.subst0 u B)
      = Tm.subst0 (Tm.subst σ u) (Tm.subst (Tm.upSub σ) B) := by
  unfold Tm.subst0
  rw [subst_subst]
  conv =>
    rhs
    rw [subst_subst]
  congr 1
  exact subst0_fun_comp σ u

/-! ## The simple fragment -/

/-- The simply-typed and function-type fragment of the syntax.  It excludes
the inductive type formers whose typing rules contain the `substMany`
side conditions; those are handled separately by `Mltt.Weaken` for `Eq`. -/
inductive Simple : Tm → Prop
  | var (x : Nat) : Simple (.var x)
  | sort (i : Nat) : Simple (.sort i)
  | pi {A B : Tm} : Simple A → Simple B → Simple (.pi A B)
  | lam {A t : Tm} : Simple A → Simple t → Simple (.lam A t)
  | app {t u : Tm} : Simple t → Simple u → Simple (.app t u)

namespace Simple

theorem rename {t : Tm} (hs : Simple t) (ρ : Nat → Nat) :
    Simple (Tm.rename ρ t) := by
  induction hs generalizing ρ with
  | var x => simpa [Tm.rename] using var (ρ x)
  | sort i => simpa [Tm.rename] using sort i
  | pi hA hB ihA ihB =>
      simp only [Tm.rename]
      exact pi (ihA ρ) (ihB (Tm.upRen ρ))
  | lam hA ht ihA iht =>
      simp only [Tm.rename]
      exact lam (ihA ρ) (iht (Tm.upRen ρ))
  | app ht hu iht ihu =>
      simp only [Tm.rename]
      exact app (iht ρ) (ihu ρ)

theorem shift {t : Tm} (hs : Simple t) (d c : Nat) : Simple (Tm.shift d c t) :=
  rename hs (Tm.shiftSub d c)

theorem upSub {σ : Nat → Tm} (hσ : ∀ x, Simple (σ x)) (x : Nat) :
    Simple (Tm.upSub σ x) := by
  cases x with
  | zero => exact var 0
  | succ y => simpa [Tm.upSub] using shift (hσ y) 1 0

theorem upSubN {σ : Nat → Tm} (hσ : ∀ x, Simple (σ x)) (m x : Nat) :
    Simple (Tm.upSubN m σ x) := by
  induction m generalizing x with
  | zero => exact hσ x
  | succ m ih => simpa [Tm.upSubN] using upSub ih x

end Simple

end Transport.Mltt.Subst
