import Transport.Mltt.Core

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Transport.Mltt.Weaken

open Transport.Mltt

/-- Adding an unused context binder shifts both the term and its type, and
preserves typing for the `Eq` family. -/
def hasType_weaken : Prop :=
  ∀ {Γ : Ctx} {A B : Tm} {t : Tm},
    HasType [Eq_sig] Γ t A →
    HasType [Eq_sig] (B :: Γ) (Tm.shift 1 0 t) (Tm.shift 1 0 A)

/-! ### Structural induction on `Tm` measured by `Tm.size` -/

theorem tm_strong_induction {P : Tm → Prop}
    (step : ∀ t, (∀ s, Tm.size s < Tm.size t → P s) → P t) : ∀ t, P t := by
  intro t
  have key : ∀ n, ∀ t, Tm.size t = n → P t := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro t ht
      apply step t
      intro s hs
      exact ih (Tm.size s) (by omega) s rfl
  exact key (Tm.size t) t rfl

theorem size_le_foldr (l : List Tm) (a : Tm) (ha : a ∈ l) :
    Tm.size a ≤ l.foldr (fun u n => Tm.size u + n) 0 := by
  induction l with
  | nil => cases ha
  | cons b bs ih =>
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp
      · have h := ih ha
        simp only [List.foldr_cons]
        omega

theorem size_lt_pi_left (A B : Tm) : Tm.size A < Tm.size (Tm.pi A B) := by
  simp only [Tm.size]; omega
theorem size_lt_pi_right (A B : Tm) : Tm.size B < Tm.size (Tm.pi A B) := by
  simp only [Tm.size]; omega
theorem size_lt_lam_left (A B : Tm) : Tm.size A < Tm.size (Tm.lam A B) := by
  simp only [Tm.size]; omega
theorem size_lt_lam_right (A B : Tm) : Tm.size B < Tm.size (Tm.lam A B) := by
  simp only [Tm.size]; omega
theorem size_lt_app_left (A B : Tm) : Tm.size A < Tm.size (Tm.app A B) := by
  simp only [Tm.size]; omega
theorem size_lt_app_right (A B : Tm) : Tm.size B < Tm.size (Tm.app A B) := by
  simp only [Tm.size]; omega
theorem size_lt_fix_left (A B : Tm) : Tm.size A < Tm.size (Tm.fix A B) := by
  simp only [Tm.size]; omega
theorem size_lt_fix_right (A B : Tm) : Tm.size B < Tm.size (Tm.fix A B) := by
  simp only [Tm.size]; omega

theorem size_lt_ind_mem {I : Nat} {args : List Tm} {a : Tm} (ha : a ∈ args) :
    Tm.size a < Tm.size (Tm.ind I args) := by
  have h := size_le_foldr args a ha
  simp only [Tm.size]; omega

theorem size_lt_roll_mem {I c : Nat} {args : List Tm} {a : Tm} (ha : a ∈ args) :
    Tm.size a < Tm.size (Tm.roll I c args) := by
  have h := size_le_foldr args a ha
  simp only [Tm.size]; omega

theorem size_lt_case_scrut (I n : Nat) (scrut C : Tm) (brs : List Tm) :
    Tm.size scrut < Tm.size (Tm.case I n scrut C brs) := by
  simp only [Tm.size]; omega

theorem size_lt_case_motive (I n : Nat) (scrut C : Tm) (brs : List Tm) :
    Tm.size C < Tm.size (Tm.case I n scrut C brs) := by
  simp only [Tm.size]; omega

theorem size_lt_case_mem {I n : Nat} {scrut C : Tm} {brs : List Tm} {a : Tm}
    (ha : a ∈ brs) :
    Tm.size a < Tm.size (Tm.case I n scrut C brs) := by
  have h := size_le_foldr brs a ha
  simp only [Tm.size]; omega



/-! ### Renaming algebra -/

theorem upRen_comp (f g : Nat → Nat) :
    (fun x => Tm.upRen f (Tm.upRen g x)) = Tm.upRen (fun x => f (g x)) := by
  funext x
  cases x with
  | zero => rfl
  | succ y => simp [Tm.upRen]

theorem upRenN_succ (m : Nat) (f : Nat → Nat) :
    Tm.upRenN (m + 1) f = Tm.upRen (Tm.upRenN m f) := rfl

theorem upRenN_comp (m : Nat) (f g : Nat → Nat) :
    (fun x => Tm.upRenN m f (Tm.upRenN m g x)) = Tm.upRenN m (fun x => f (g x)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      funext x
      rw [upRenN_succ, upRenN_succ, upRenN_succ]
      rw [congrFun (upRen_comp (Tm.upRenN m f) (Tm.upRenN m g)) x, ih]

theorem rename_comp (t : Tm) (f g : Nat → Nat) :
    Tm.rename f (Tm.rename g t) = Tm.rename (fun x => f (g x)) t := by
  revert f g t
  apply tm_strong_induction
  intro t ih f g
  cases t with
  | var x => simp [Tm.rename]
  | sort i => simp [Tm.rename]
  | pi A B =>
      simp only [Tm.rename]
      rw [ih A (size_lt_pi_left A B) f g,
          ih B (size_lt_pi_right A B) (Tm.upRen f) (Tm.upRen g), upRen_comp]
  | lam A B =>
      simp only [Tm.rename]
      rw [ih A (size_lt_lam_left A B) f g,
          ih B (size_lt_lam_right A B) (Tm.upRen f) (Tm.upRen g), upRen_comp]
  | app A B =>
      simp only [Tm.rename]
      rw [ih A (size_lt_app_left A B) f g, ih B (size_lt_app_right A B) f g]
  | fix A B =>
      simp only [Tm.rename]
      rw [ih A (size_lt_fix_left A B) f g,
          ih B (size_lt_fix_right A B) (Tm.upRen f) (Tm.upRen g), upRen_comp]
  | ind I args =>
      simp only [Tm.rename]
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih a (size_lt_ind_mem ha) f g
  | roll I c args =>
      simp only [Tm.rename]
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih a (size_lt_roll_mem ha) f g
  | case I n scrut C brs =>
      simp only [Tm.rename]
      rw [ih scrut (size_lt_case_scrut I n scrut C brs) f g,
          ih C (size_lt_case_motive I n scrut C brs) (Tm.upRenN (n+1) f) (Tm.upRenN (n+1) g),
          upRenN_comp]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact ih a (size_lt_case_mem ha) f g


theorem rename_upRenN_shift (m : Nat) (f : Nat → Nat) (t : Tm) :
    Tm.rename (Tm.upRenN (m + 1) f) (Tm.shift 1 0 t)
      = Tm.shift 1 0 (Tm.rename (Tm.upRenN m f) t) := by
  simp only [Tm.shift]
  rw [rename_comp t (Tm.upRenN (m+1) f) (Tm.shiftSub 1 0),
      rename_comp t (Tm.shiftSub 1 0) (Tm.upRenN m f)]
  have h : (fun x => Tm.upRenN (m + 1) f (Tm.shiftSub 1 0 x))
      = (fun x => Tm.shiftSub 1 0 (Tm.upRenN m f x)) := by
    funext x
    rw [upRenN_succ]
    simp [Tm.shiftSub, Tm.upRen]
  rw [h]

theorem upSubN_succ (m : Nat) (σ : Nat → Tm) :
    Tm.upSubN (m + 1) σ = Tm.upSub (Tm.upSubN m σ) := rfl

theorem rename_upSub (f : Nat → Nat) (σ : Nat → Tm) (x : Nat) :
    Tm.rename (Tm.upRen f) (Tm.upSub σ x)
      = Tm.upSub (fun y => Tm.rename f (σ y)) x := by
  cases x with
  | zero => simp [Tm.upSub, Tm.upRen, Tm.rename]
  | succ y =>
      simp only [Tm.upSub]
      simpa [Tm.upRenN] using rename_upRenN_shift 0 f (σ y)

theorem rename_upSubN (m : Nat) (f : Nat → Nat) (σ : Nat → Tm) (x : Nat) :
    Tm.rename (Tm.upRenN m f) (Tm.upSubN m σ x)
      = Tm.upSubN m (fun y => Tm.rename f (σ y)) x := by
  induction m generalizing x with
  | zero => simp [Tm.upSubN, Tm.upRenN]
  | succ m ih =>
      rw [upRenN_succ, upSubN_succ, upSubN_succ, rename_upSub]
      congr 1
      funext y
      exact ih y

theorem upSub_rename (σ : Nat → Tm) (f : Nat → Nat) (x : Nat) :
    Tm.upSub σ (Tm.upRen f x) = Tm.upSub (fun y => σ (f y)) x := by
  cases x with
  | zero => simp [Tm.upSub, Tm.upRen]
  | succ y => simp [Tm.upSub, Tm.upRen]

theorem upSubN_rename (m : Nat) (σ : Nat → Tm) (f : Nat → Nat) (x : Nat) :
    Tm.upSubN m σ (Tm.upRenN m f x) = Tm.upSubN m (fun y => σ (f y)) x := by
  induction m generalizing x with
  | zero => simp [Tm.upSubN, Tm.upRenN]
  | succ m ih =>
      rw [upRenN_succ, upSubN_succ, upSubN_succ, upSub_rename]
      congr 1
      funext y
      exact ih y


theorem upSub_renameFn (f : Nat → Nat) (σ : Nat → Tm) :
    (fun x => Tm.rename (Tm.upRen f) (Tm.upSub σ x))
      = Tm.upSub (fun y => Tm.rename f (σ y)) :=
  funext (rename_upSub f σ)

theorem upSubN_renameFn (m : Nat) (f : Nat → Nat) (σ : Nat → Tm) :
    (fun x => Tm.rename (Tm.upRenN m f) (Tm.upSubN m σ x))
      = Tm.upSubN m (fun y => Tm.rename f (σ y)) :=
  funext (rename_upSubN m f σ)

theorem upSub_renameComp (σ : Nat → Tm) (f : Nat → Nat) :
    (fun x => Tm.upSub σ (Tm.upRen f x)) = Tm.upSub (fun y => σ (f y)) :=
  funext (upSub_rename σ f)

theorem upSubN_renameComp (m : Nat) (σ : Nat → Tm) (f : Nat → Nat) :
    (fun x => Tm.upSubN m σ (Tm.upRenN m f x)) = Tm.upSubN m (fun y => σ (f y)) :=
  funext (upSubN_rename m σ f)

theorem rename_subst (t : Tm) (f : Nat → Nat) (σ : Nat → Tm) :
    Tm.rename f (Tm.subst σ t) = Tm.subst (fun x => Tm.rename f (σ x)) t := by
  revert f σ t
  apply tm_strong_induction
  intro t ih f σ
  cases t with
  | var x => simp [Tm.subst, Tm.rename]
  | sort i => simp [Tm.subst, Tm.rename]
  | pi A B =>
      simp only [Tm.subst, Tm.rename]
      rw [ih A (size_lt_pi_left A B) f σ,
          ih B (size_lt_pi_right A B) (Tm.upRen f) (Tm.upSub σ),
          upSub_renameFn]
  | lam A B =>
      simp only [Tm.subst, Tm.rename]
      rw [ih A (size_lt_lam_left A B) f σ,
          ih B (size_lt_lam_right A B) (Tm.upRen f) (Tm.upSub σ),
          upSub_renameFn]
  | app A B =>
      simp only [Tm.subst, Tm.rename]
      rw [ih A (size_lt_app_left A B) f σ, ih B (size_lt_app_right A B) f σ]
  | fix A B =>
      simp only [Tm.subst, Tm.rename]
      rw [ih A (size_lt_fix_left A B) f σ,
          ih B (size_lt_fix_right A B) (Tm.upRen f) (Tm.upSub σ),
          upSub_renameFn]
  | ind I args =>
      simp only [Tm.subst, Tm.rename]
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih a (size_lt_ind_mem ha) f σ
  | roll I c args =>
      simp only [Tm.subst, Tm.rename]
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih a (size_lt_roll_mem ha) f σ
  | case I n scrut C brs =>
      simp only [Tm.subst, Tm.rename]
      rw [ih scrut (size_lt_case_scrut I n scrut C brs) f σ,
          ih C (size_lt_case_motive I n scrut C brs)
            (Tm.upRenN (n+1) f) (Tm.upSubN (n+1) σ),
          upSubN_renameFn]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact ih a (size_lt_case_mem ha) f σ

theorem subst_rename (t : Tm) (σ : Nat → Tm) (f : Nat → Nat) :
    Tm.subst σ (Tm.rename f t) = Tm.subst (fun x => σ (f x)) t := by
  revert σ f t
  apply tm_strong_induction
  intro t ih σ f
  cases t with
  | var x => simp [Tm.subst, Tm.rename]
  | sort i => simp [Tm.subst, Tm.rename]
  | pi A B =>
      simp only [Tm.subst, Tm.rename]
      rw [ih A (size_lt_pi_left A B) σ f,
          ih B (size_lt_pi_right A B) (Tm.upSub σ) (Tm.upRen f),
          upSub_renameComp]
  | lam A B =>
      simp only [Tm.subst, Tm.rename]
      rw [ih A (size_lt_lam_left A B) σ f,
          ih B (size_lt_lam_right A B) (Tm.upSub σ) (Tm.upRen f),
          upSub_renameComp]
  | app A B =>
      simp only [Tm.subst, Tm.rename]
      rw [ih A (size_lt_app_left A B) σ f, ih B (size_lt_app_right A B) σ f]
  | fix A B =>
      simp only [Tm.subst, Tm.rename]
      rw [ih A (size_lt_fix_left A B) σ f,
          ih B (size_lt_fix_right A B) (Tm.upSub σ) (Tm.upRen f),
          upSub_renameComp]
  | ind I args =>
      simp only [Tm.subst, Tm.rename]
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih a (size_lt_ind_mem ha) σ f
  | roll I c args =>
      simp only [Tm.subst, Tm.rename]
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih a (size_lt_roll_mem ha) σ f
  | case I n scrut C brs =>
      simp only [Tm.subst, Tm.rename]
      rw [ih scrut (size_lt_case_scrut I n scrut C brs) σ f,
          ih C (size_lt_case_motive I n scrut C brs)
            (Tm.upSubN (n+1) σ) (Tm.upRenN (n+1) f),
          upSubN_renameComp]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact ih a (size_lt_case_mem ha) σ f


theorem upRenN_lt (m : Nat) (f : Nat → Nat) {x : Nat} (h : x < m) :
    Tm.upRenN m f x = x := by
  induction m generalizing x with
  | zero => omega
  | succ m ih =>
      rw [upRenN_succ]
      cases x with
      | zero => simp [Tm.upRen]
      | succ y =>
          have hy : y < m := by omega
          simp [Tm.upRen, ih hy]

theorem upRenN_ge (m : Nat) (f : Nat → Nat) {x : Nat} (h : m ≤ x) :
    Tm.upRenN m f x = f (x - m) + m := by
  induction m generalizing x with
  | zero => simp [Tm.upRenN]
  | succ m ih =>
      rw [upRenN_succ]
      cases x with
      | zero => omega
      | succ y =>
          have hy : m ≤ y := by omega
          simp only [Tm.upRen, ih hy, Nat.succ_sub_succ]
          omega

def substFun (xs : List Tm) (x : Nat) : Tm :=
  match xs[x]? with
  | some u => u
  | none => Tm.var (x - xs.length)

theorem substMany_eq_subst (xs : List Tm) (t : Tm) :
    substMany xs t = Tm.subst (substFun xs) t := rfl

theorem rename_substMany_fun (f : Nat → Nat) (xs : List Tm) (x : Nat) :
    Tm.rename f (substFun xs x)
      = substFun (xs.map (Tm.rename f)) (Tm.upRenN xs.length f x) := by
  unfold substFun
  by_cases hx : x < xs.length
  · have hx' : x < (xs.map (Tm.rename f)).length := by
      simpa [List.length_map] using hx
    rw [List.getElem?_eq_getElem hx, upRenN_lt _ _ hx, List.getElem?_eq_getElem hx']
    simp [List.getElem_map]
  · have hle : xs.length ≤ x := by omega
    have hnone : xs[x]? = none := List.getElem?_eq_none hle
    rw [hnone]
    have hge : (xs.map (Tm.rename f)).length ≤ Tm.upRenN xs.length f x := by
      rw [List.length_map, upRenN_ge _ _ hle]
      omega
    rw [List.getElem?_eq_none hge]
    have hsub : Tm.upRenN xs.length f x - (xs.map (Tm.rename f)).length
        = f (x - xs.length) := by
      rw [List.length_map, upRenN_ge _ _ hle]
      omega
    rw [hsub]
    simp [Tm.rename]

theorem rename_substMany (t : Tm) (f : Nat → Nat) (xs : List Tm) :
    Tm.rename f (substMany xs t)
      = substMany (xs.map (Tm.rename f)) (Tm.rename (Tm.upRenN xs.length f) t) := by
  rw [substMany_eq_subst, substMany_eq_subst, rename_subst, subst_rename]
  congr 1
  funext x
  exact rename_substMany_fun f xs x


/-! ### Context weakening relation -/

def Wk (ρ : Nat → Nat) (Γ Δ : Ctx) : Prop :=
  ∀ x A, ctxLookup Γ x = some A → ctxLookup Δ (ρ x) = some (Tm.rename ρ A)

theorem Wk_extend {ρ : Nat → Nat} {Γ Δ : Ctx} (h : Wk ρ Γ Δ) (A : Tm) :
    Wk (Tm.upRen ρ) (A :: Γ) (Tm.rename ρ A :: Δ) := by
  intro x B hx
  cases x with
  | zero =>
      simp only [ctxLookup, Option.some.injEq] at hx
      subst hx
      simp only [ctxLookup, Tm.upRen]
      have hsh : Tm.rename (Tm.upRen ρ) (Tm.shift 1 0 A)
          = Tm.shift 1 0 (Tm.rename ρ A) := by
        simpa [Tm.upRenN] using rename_upRenN_shift 0 ρ A
      rw [hsh]
  | succ y =>
      simp only [ctxLookup] at hx
      cases hl : ctxLookup Γ y with
      | none => simp [hl] at hx
      | some A0 =>
          simp [hl] at hx
          subst hx
          have h0 := h y A0 hl
          simp only [ctxLookup, Tm.upRen]
          rw [h0]
          simp only [Option.map_some]
          have hsh : Tm.rename (Tm.upRen ρ) (Tm.shift 1 0 A0)
              = Tm.shift 1 0 (Tm.rename ρ A0) := by
            simpa [Tm.upRenN] using rename_upRenN_shift 0 ρ A0
          rw [hsh]

theorem Wk_insert_front (B : Tm) (Γ : Ctx) :
    Wk (Tm.shiftSub 1 0) Γ (B :: Γ) := by
  intro x A hx
  simp only [Tm.shiftSub]
  rw [if_neg (Nat.not_lt_zero x)]
  simp only [ctxLookup, hx]
  rfl

theorem subst0_eq_substMany (u : Tm) (t : Tm) :
    Tm.subst0 u t = substMany [u] t := by
  unfold Tm.subst0 substMany
  congr 1
  funext x
  cases x with
  | zero => simp
  | succ y => simp

theorem lookupIndStrict_Eq_sig {I : Nat} {sig : IndSig}
    (h : lookupIndStrict [Eq_sig] I = some sig) : sig = Eq_sig := by
  unfold lookupIndStrict lookupInd lookup at h
  cases I with
  | zero =>
      by_cases hp : strictlyPositive 0 Eq_sig = true
      · simp [hp] at h
        exact h.symm
      · simp [hp] at h
  | succ I => simp at h

def eqCtor : CtorSig :=
  { paramTys := [], recArgs := [], indices := [Tm.var 0] }

theorem lookupCtor_Eq_sig {c : Nat} {ctor : CtorSig}
    (h : lookupCtor Eq_sig c = some ctor) : ctor = eqCtor := by
  unfold lookupCtor lookup at h
  cases c with
  | zero =>
      simp [Eq_sig] at h
      simpa [eqCtor] using h.symm
  | succ c => simp [Eq_sig] at h


/-! ### Shifting through higher renamings -/

theorem upRenN_comp_shiftSub (m : Nat) (ρ : Nat → Nat) :
    (fun x => Tm.upRenN m ρ (Tm.shiftSub m 0 x))
      = (fun x => Tm.shiftSub m 0 (ρ x)) := by
  funext x
  simp only [Tm.shiftSub]
  rw [if_neg (Nat.not_lt_zero x)]
  have hle : m ≤ x + m := by omega
  rw [upRenN_ge m ρ hle]
  simp [Nat.add_sub_cancel]

theorem rename_upRenN_shift_ge (m : Nat) (ρ : Nat → Nat) (t : Tm) :
    Tm.rename (Tm.upRenN m ρ) (Tm.shift m 0 t) = Tm.shift m 0 (Tm.rename ρ t) := by
  simp only [Tm.shift]
  rw [rename_comp t (Tm.upRenN m ρ) (Tm.shiftSub m 0),
      rename_comp t (Tm.shiftSub m 0) ρ]
  rw [upRenN_comp_shiftSub]

def caseScrutType (I : Nat) (params : List Tm) : Tm :=
  .ind I (params.map (Tm.shift 1 0) ++ [Tm.var 0])

theorem caseScrutType_rename (ρ : Nat → Nat) (I : Nat) (params : List Tm) :
    caseScrutType I (params.map (Tm.rename ρ))
      = Tm.rename (Tm.upRen ρ) (caseScrutType I params) := by
  unfold caseScrutType
  simp only [Tm.rename]
  congr 1
  rw [List.map_append, List.map_map, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro p hp
    have h := rename_upRenN_shift 0 ρ p
    simpa [Tm.upRenN] using h.symm
  · simp [Tm.rename, Tm.upRen]

def caseMotiveCtxEq (Γ : Ctx) (I : Nat) (params : List Tm) : Ctx :=
  caseScrutType I params :: substParams params (Tm.var 1) :: Γ

theorem caseMotiveCtx_Eq_sig (Γ : Ctx) (I : Nat) (params : List Tm) :
    caseMotiveCtx Γ I Eq_sig params = caseMotiveCtxEq Γ I params := by
  unfold caseMotiveCtx caseMotiveCtxEq caseScrutType
  simp [Eq_sig, ctxExtendMany, ctxExtend, List.range_succ]

theorem substParams_var1_rename (params : List Tm) (hp : params.length = 2)
    (ρ : Nat → Nat) :
    substParams (params.map (Tm.rename ρ)) (Tm.var 1)
      = Tm.rename ρ (substParams params (Tm.var 1)) := by
  unfold substParams
  rw [← List.map_reverse]
  rw [rename_substMany (Tm.var 1) ρ params.reverse]
  rw [List.length_reverse, hp]
  have hv : Tm.rename (Tm.upRenN 2 ρ) (Tm.var 1) = Tm.var 1 := by
    simp only [Tm.rename]
    rw [upRenN_lt 2 ρ (by omega : 1 < 2)]
  rw [hv]

theorem caseMotiveCtx_wk {ρ : Nat → Nat} {Γ Δ : Ctx} (h : Wk ρ Γ Δ)
    (I : Nat) (params : List Tm) (hp : params.length = 2) :
    Wk (Tm.upRenN 2 ρ) (caseMotiveCtxEq Γ I params)
      (caseMotiveCtxEq Δ I (params.map (Tm.rename ρ))) := by
  intro x A hx
  simp only [caseMotiveCtxEq] at hx ⊢
  cases x with
  | zero =>
      simp only [ctxLookup, Option.map_some] at hx
      cases hx
      rw [upRenN_lt 2 ρ (by omega : 0 < 2)]
      simp only [ctxLookup]
      have hS : Tm.rename (Tm.upRenN 1 ρ) (caseScrutType I params)
          = caseScrutType I (params.map (Tm.rename ρ)) := by
        simpa [Tm.upRenN] using (caseScrutType_rename ρ I params).symm
      rw [← hS, rename_upRenN_shift]
  | succ y =>
      cases y with
      | zero =>
          simp only [ctxLookup, Option.map_some] at hx
          cases hx
          rw [upRenN_lt 2 ρ (by omega : 1 < 2)]
          simp only [ctxLookup, Option.map_some]
          have hA : substParams (params.map (Tm.rename ρ)) (Tm.var 1)
              = Tm.rename ρ (substParams params (Tm.var 1)) :=
            substParams_var1_rename params hp ρ
          rw [hA, rename_upRenN_shift, rename_upRenN_shift]
          simp [Tm.upRenN]
      | succ z =>
          simp only [ctxLookup, Option.map_some] at hx
          cases hl : ctxLookup Γ z with
          | none => simp [hl] at hx
          | some A0 =>
              simp [hl] at hx
              cases hx
              have h0 := h z A0 hl
              have hle : 2 ≤ z + 2 := by omega
              rw [upRenN_ge 2 ρ hle]
              have hz : z + 2 - 2 = z := by omega
              rw [hz]
              simp only [ctxLookup, Option.map_some]
              rw [h0]
              simp only [Option.map_some]
              rw [rename_upRenN_shift, rename_upRenN_shift]
              simp [Tm.upRenN]


theorem substParams_var_rename (params : List Tm) (hp : params.length = 2)
    (ρ : Nat → Nat) (k : Nat) (hk : k < 2) :
    substParams (params.map (Tm.rename ρ)) (Tm.var k)
      = Tm.rename ρ (substParams params (Tm.var k)) := by
  unfold substParams
  rw [← List.map_reverse]
  rw [rename_substMany (Tm.var k) ρ params.reverse]
  rw [List.length_reverse, hp]
  have hv : Tm.rename (Tm.upRenN 2 ρ) (Tm.var k) = Tm.var k := by
    simp only [Tm.rename]
    rw [upRenN_lt 2 ρ hk]
  rw [hv]

theorem branch_map {brs : List Tm} {f : Tm → Tm} {c : Nat} {br' : Tm}
    (h : Tm.branch (brs.map f) c = some br') :
    ∃ br, Tm.branch brs c = some br ∧ f br = br' := by
  unfold Tm.branch at h
  rw [List.getElem?_map] at h
  cases hb : brs[c]? with
  | none => simp [hb] at h
  | some br => simp [hb] at h; exact ⟨br, hb, h⟩

def indTyList (args : List Tm) : List Tm :=
  Eq_sig.params.map (substMany args) ++
    Eq_sig.indices.map (substParams (args.take Eq_sig.params.length))

theorem indTyList_rename (args : List Tm) (hlen : args.length = 3)
    (ρ : Nat → Nat) :
    indTyList (args.map (Tm.rename ρ)) = (indTyList args).map (Tm.rename ρ) := by
  unfold indTyList
  rw [List.map_append]
  congr 1
  · rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    change substMany (args.map (Tm.rename ρ)) p = Tm.rename ρ (substMany args p)
    rw [rename_substMany p ρ args, hlen]
    have hp' : p = Tm.sort 0 ∨ p = Tm.var 0 := by
      simpa [Eq_sig] using hp
    rcases hp' with rfl | rfl
    · simp [Tm.rename]
    · simp only [Tm.rename]
      rw [upRenN_lt 3 ρ (by omega : 0 < 3)]
  · rw [List.map_map]
    apply List.map_congr_left
    intro d hd
    have hd' : d = Tm.var 1 := by simpa [Eq_sig] using hd
    subst hd'
    rw [← List.map_take]
    exact substParams_var_rename (args.take 2)
      (by simp [List.length_take, hlen]) ρ 1 (by omega)

def rollIndexArgs (ctor : CtorSig) (p : Nat) (args : List Tm) : List Tm :=
  args.take p ++ ctor.indices.map (substParams (args.take p))

theorem rollIndexArgs_eqCtor_rename (args : List Tm) (hlen : args.length = 2)
    (ρ : Nat → Nat) :
    rollIndexArgs eqCtor 2 (args.map (Tm.rename ρ))
      = (rollIndexArgs eqCtor 2 args).map (Tm.rename ρ) := by
  unfold rollIndexArgs eqCtor
  rw [List.map_append]
  congr 1
  · rw [← List.map_take]
  · simp only [List.map_cons, List.map_nil]
    rw [← List.map_take]
    simpa using substParams_var_rename (args.take 2)
      (by simp [List.length_take, hlen]) ρ 0 (by omega)


theorem paramsTyList_rename (args : List Tm) (hlen : 0 < args.length)
    (ρ : Nat → Nat) :
    Eq_sig.params.map (substMany (args.map (Tm.rename ρ)))
      = (Eq_sig.params.map (substMany args)).map (Tm.rename ρ) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro p hp
  change substMany (args.map (Tm.rename ρ)) p = Tm.rename ρ (substMany args p)
  rw [rename_substMany p ρ args]
  have hp' : p = Tm.sort 0 ∨ p = Tm.var 0 := by
    simpa [Eq_sig] using hp
  rcases hp' with rfl | rfl
  · simp [Tm.rename]
  · simp only [Tm.rename]
    rw [upRenN_lt args.length ρ hlen]

theorem indicesTyList_rename (args : List Tm) (hlen : args.length = 3)
    (ρ : Nat → Nat) :
    Eq_sig.indices.map (substParams (args.map (Tm.rename ρ) |>.take 2))
      = (Eq_sig.indices.map (substParams (args.take 2))).map (Tm.rename ρ) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro d hd
  have hd' : d = Tm.var 1 := by simpa [Eq_sig] using hd
  subst hd'
  rw [← List.map_take]
  exact substParams_var_rename (args.take 2)
    (by simp [List.length_take, hlen]) ρ 1 (by omega)

theorem hasType_rename {Γ : Ctx} {t A : Tm}
    (h : HasType [Eq_sig] Γ t A) :
    ∀ (ρ : Nat → Nat) (Δ : Ctx), Wk ρ Γ Δ →
      HasType [Eq_sig] Δ (Tm.rename ρ t) (Tm.rename ρ A) := by
  induction h with
  | var Γ x A hx =>
      intro ρ Δ hwk
      simp only [Tm.rename]
      exact HasType.var Δ (ρ x) (Tm.rename ρ A) (hwk x A hx)
  | sort Γ i =>
      intro ρ Δ _
      simpa [Tm.rename] using HasType.sort Δ i
  | pi Γ A B i j hA hB ihA ihB =>
      intro ρ Δ hwk
      simp only [Tm.rename]
      have h1 : HasType [Eq_sig] Δ (Tm.rename ρ A) (Tm.sort i) := by
        simpa [Tm.rename] using ihA ρ Δ hwk
      have h2 : HasType [Eq_sig] (Tm.rename ρ A :: Δ)
          (Tm.rename (Tm.upRen ρ) B) (Tm.sort j) := by
        simpa [Tm.rename] using ihB (Tm.upRen ρ) (Tm.rename ρ A :: Δ) (Wk_extend hwk A)
      exact HasType.pi Δ (Tm.rename ρ A) (Tm.rename (Tm.upRen ρ) B) i j h1 h2
  | lam Γ A t B i hA ht ihA iht =>
      intro ρ Δ hwk
      simp only [Tm.rename]
      have h1 : HasType [Eq_sig] Δ (Tm.rename ρ A) (Tm.sort i) := by
        simpa [Tm.rename] using ihA ρ Δ hwk
      have h2 : HasType [Eq_sig] (Tm.rename ρ A :: Δ)
          (Tm.rename (Tm.upRen ρ) t) (Tm.rename (Tm.upRen ρ) B) := by
        simpa [Tm.rename] using iht (Tm.upRen ρ) (Tm.rename ρ A :: Δ) (Wk_extend hwk A)
      exact HasType.lam Δ (Tm.rename ρ A) (Tm.rename (Tm.upRen ρ) t)
        (Tm.rename (Tm.upRen ρ) B) i h1 h2
  | app Γ t u A B ht hu iht ihu =>
      intro ρ Δ hwk
      simp only [Tm.rename]
      have h1 : HasType [Eq_sig] Δ (Tm.rename ρ t)
          (Tm.pi (Tm.rename ρ A) (Tm.rename (Tm.upRen ρ) B)) := by
        simpa [Tm.rename] using iht ρ Δ hwk
      have h2 : HasType [Eq_sig] Δ (Tm.rename ρ u) (Tm.rename ρ A) := by
        simpa [Tm.rename] using ihu ρ Δ hwk
      have h := HasType.app Δ (Tm.rename ρ t) (Tm.rename ρ u)
        (Tm.rename ρ A) (Tm.rename (Tm.upRen ρ) B) h1 h2
      rw [subst0_eq_substMany] at h
      rw [subst0_eq_substMany, rename_substMany]
      simpa [Tm.upRenN] using h
  | ind Γ I sig args hsig hlen hargs ihargs =>
      intro ρ Δ hwk
      simp only [Tm.rename]
      have hsigeq : sig = Eq_sig := lookupIndStrict_Eq_sig hsig
      subst hsigeq
      have hlen3 : args.length = 3 := by simpa [Eq_sig] using hlen
      refine HasType.ind Δ I Eq_sig (args.map (Tm.rename ρ)) hsig ?_ ?_
      · simpa [List.length_map] using hlen
      · intro i a A ha hA
        change (indTyList (args.map (Tm.rename ρ)))[i]? = some A at hA
        rw [indTyList_rename args hlen3 ρ, List.getElem?_map] at hA
        rw [List.getElem?_map] at ha
        cases harg : args[i]? with
        | none => simp [harg] at ha
        | some a0 =>
            simp [harg] at ha
            cases htyp : (indTyList args)[i]? with
            | none => simp [htyp] at hA
            | some A0 =>
                simp [htyp] at hA
                have h1 := ihargs i a0 A0 harg htyp ρ Δ hwk
                cases ha
                cases hA
                exact h1
  | roll Γ I sig c ctor args hsig hctor hlen hparams hctys hrec ihparams ihctys ihrec =>
      intro ρ Δ hwk
      simp only [Tm.rename]
      have hsigeq : sig = Eq_sig := lookupIndStrict_Eq_sig hsig
      subst hsigeq
      have hctoreq : ctor = eqCtor := lookupCtor_Eq_sig hctor
      subst hctoreq
      have hlen2 : args.length = 2 := by simpa [Eq_sig, eqCtor] using hlen
      change HasType [Eq_sig] Δ (Tm.roll I c (args.map (Tm.rename ρ)))
        (Tm.ind I ((rollIndexArgs eqCtor 2 args).map (Tm.rename ρ)))
      rw [← rollIndexArgs_eqCtor_rename args hlen2 ρ]
      refine HasType.roll Δ I Eq_sig c eqCtor (args.map (Tm.rename ρ)) hsig hctor ?_ ?_ ?_ ?_
      · simpa [eqCtor, List.length_map] using hlen
      · intro i a A ha hA
        rw [paramsTyList_rename args (by omega : 0 < args.length) ρ, List.getElem?_map] at hA
        rw [← List.map_take, List.getElem?_map] at ha
        cases harg : (args.take Eq_sig.params.length)[i]? with
        | none => rw [harg] at ha; simp at ha
        | some a0 =>
            rw [harg] at ha
            simp only [Option.map_some, Option.some.injEq] at ha
            cases htyp : (Eq_sig.params.map (substMany args))[i]? with
            | none => rw [htyp] at hA; simp at hA
            | some A0 =>
                rw [htyp] at hA
                simp only [Option.map_some, Option.some.injEq] at hA
                have h1 := ihparams i a0 A0 harg htyp ρ Δ hwk
                rw [ha] at h1
                rw [hA] at h1
                exact h1
      · intro i a A ha _
        simp [eqCtor] at ha
      · intro i r idxs _ hidx
        simp [eqCtor] at hidx
  | case Γ I n sig scrut C brs i args hsig hn hlen hscrut hmotive hbrs hbranch ihscrut ihmotive ihbranch =>
      intro ρ Δ hwk
      simp only [Tm.rename]
      have hsigeq : sig = Eq_sig := lookupIndStrict_Eq_sig hsig
      subst hsigeq
      have hn1 : n = 1 := by simpa [Eq_sig] using hn
      subst hn1
      have hlen3 : args.length = 3 := by simpa [Eq_sig] using hlen
      have hp2 : (args.take 2).length = 2 := by simp [List.length_take, hlen3]
      have hp2' : ((args.map (Tm.rename ρ)).take 2).length = 2 := by
        rw [← List.map_take]; simpa [List.length_map] using hp2
      -- scrutinee
      have hscrut' : HasType [Eq_sig] Δ (Tm.rename ρ scrut)
          (.ind I (args.map (Tm.rename ρ))) := by
        simpa [Tm.rename] using ihscrut ρ Δ hwk
      -- motive
      have hwkC : Wk (Tm.upRenN 2 ρ) (caseMotiveCtx Γ I Eq_sig (args.take 2))
          (caseMotiveCtx Δ I Eq_sig (args.map (Tm.rename ρ) |>.take 2)) := by
        have hEq : (args.take 2).map (Tm.rename ρ) = (args.map (Tm.rename ρ)).take 2 := by
          rw [List.map_take]
        have hw := caseMotiveCtx_wk hwk I (args.take 2) hp2
        rw [hEq] at hw
        rw [caseMotiveCtx_Eq_sig, caseMotiveCtx_Eq_sig]
        exact hw
      have hmotive' : HasType [Eq_sig]
          (caseMotiveCtx Δ I Eq_sig (args.map (Tm.rename ρ) |>.take 2))
          (Tm.rename (Tm.upRenN 2 ρ) C) (Tm.sort i) := by
        simpa [Tm.rename] using ihmotive (Tm.upRenN 2 ρ) _ hwkC
      -- length of branches
      have hbrs' : (brs.map (Tm.rename ρ)).length = Eq_sig.ctors.length := by
        simpa [List.length_map] using hbrs
      have hxslen : ([scrut] ++ (args.drop Eq_sig.params.length).reverse).length = 2 := by
        simp [List.length_append, List.length_reverse, List.length_drop, hlen3, Eq_sig]
      have hxsmap : ([scrut] ++ (args.drop Eq_sig.params.length).reverse).map (Tm.rename ρ)
          = [Tm.rename ρ scrut] ++
              ((args.map (Tm.rename ρ)).drop Eq_sig.params.length).reverse := by
        simp only [List.map_append, List.map_reverse, List.map_drop, List.map_cons,
          List.map_nil]
      rw [rename_substMany, hxslen, hxsmap]
      refine HasType.case Δ I 1 Eq_sig (Tm.rename ρ scrut) (Tm.rename (Tm.upRenN 2 ρ) C)
        (brs.map (Tm.rename ρ)) i (args.map (Tm.rename ρ)) hsig rfl ?_ hscrut' hmotive' hbrs' ?_
      · simp [List.length_map]
        simpa [Eq_sig] using hlen
      · intro b ctor br hctor hbr hpTys hrecTys
        have hctoreq : ctor = eqCtor := lookupCtor_Eq_sig hctor
        subst hctoreq
        have hpTys' : eqCtor.paramTys = [] := rfl
        have hrecTys' : eqCtor.recArgs = [] := rfl
        rcases branch_map hbr with ⟨br0, hbr0, hbrEq⟩
        have h0 := hbranch b eqCtor br0 hctor hbr0 hpTys' hrecTys'
        have h1 := ihbranch b eqCtor br0 hctor hbr0 hpTys' hrecTys' ρ Δ hwk
        -- branch type commutation
        rw [rename_substMany] at h1
        have hlenys : ([Tm.roll I b (args.take Eq_sig.params.length)] ++
            (eqCtor.indices.map (substParams (args.take Eq_sig.params.length))).reverse).length = 2 := by
          simp [eqCtor, Eq_sig]
        rw [hlenys] at h1
        -- target branch type
        have hys : (([Tm.roll I b (args.take Eq_sig.params.length)] ++
              (eqCtor.indices.map (substParams (args.take Eq_sig.params.length))).reverse).map (Tm.rename ρ))
            = ([Tm.roll I b ((args.map (Tm.rename ρ)).take Eq_sig.params.length)] ++
              (eqCtor.indices.map (substParams ((args.map (Tm.rename ρ)).take Eq_sig.params.length))).reverse) := by
          simp only [eqCtor, List.map_append, List.map_cons, List.map_nil]
          congr 1
          · simp [Tm.rename, List.map_take]
          · rw [← List.map_take]
            simpa using (substParams_var_rename (args.take Eq_sig.params.length) hp2 ρ 0 (by omega)).symm
        rw [hys] at h1
        cases hbrEq
        exact h1

theorem hasType_weaken_proof : hasType_weaken := by
  intro Γ A B t h
  simpa [Tm.shift] using
    hasType_rename h (Tm.shiftSub 1 0) (B :: Γ) (Wk_insert_front B Γ)

end Transport.Mltt.Weaken
