import Transport.Mltt.Core

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-!
# Inserting a binder into a context

`ctxExtend` and `ctxExtendMany` prepend binders to a context, but the case
motive needs its fresh binder placed between its index telescope and the
surrounding context.  `Ctx.insertAt` supplies that insertion, and the lemmas
below record how `ctxLookup`, `ctxExtendMany` and `caseMotiveCtx` react to it.

`ctxLookup` shifts by one for every binder it walks past, so the binder stored
at position `k` reads back shifted `k + 1` times.  The renaming algebra at the
top of the file composes those single shifts into one `Tm.shift`.
-/

namespace Transport.Mltt

/-! ## Renaming algebra

These lemmas are local to this file: `ctxLookup_insertAt_eq` needs to collapse a
stack of single shifts into one `Tm.shift`. -/

namespace Tm

private theorem strong_induction {P : Tm → Prop}
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

private theorem size_le_foldr (l : List Tm) (a : Tm) (ha : a ∈ l) :
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

private theorem size_lt_pi_left (A B : Tm) : Tm.size A < Tm.size (Tm.pi A B) := by
  simp only [Tm.size]; omega
private theorem size_lt_pi_right (A B : Tm) : Tm.size B < Tm.size (Tm.pi A B) := by
  simp only [Tm.size]; omega
private theorem size_lt_lam_left (A B : Tm) : Tm.size A < Tm.size (Tm.lam A B) := by
  simp only [Tm.size]; omega
private theorem size_lt_lam_right (A B : Tm) : Tm.size B < Tm.size (Tm.lam A B) := by
  simp only [Tm.size]; omega
private theorem size_lt_app_left (A B : Tm) : Tm.size A < Tm.size (Tm.app A B) := by
  simp only [Tm.size]; omega
private theorem size_lt_app_right (A B : Tm) : Tm.size B < Tm.size (Tm.app A B) := by
  simp only [Tm.size]; omega
private theorem size_lt_fix_left (A B : Tm) : Tm.size A < Tm.size (Tm.fix A B) := by
  simp only [Tm.size]; omega
private theorem size_lt_fix_right (A B : Tm) : Tm.size B < Tm.size (Tm.fix A B) := by
  simp only [Tm.size]; omega

private theorem size_lt_ind_mem {I : Nat} {args : List Tm} {a : Tm} (ha : a ∈ args) :
    Tm.size a < Tm.size (Tm.ind I args) := by
  have h := size_le_foldr args a ha
  simp only [Tm.size]; omega

private theorem size_lt_roll_mem {I c : Nat} {args : List Tm} {a : Tm} (ha : a ∈ args) :
    Tm.size a < Tm.size (Tm.roll I c args) := by
  have h := size_le_foldr args a ha
  simp only [Tm.size]; omega

private theorem size_lt_case_scrut (I n : Nat) (scrut C : Tm) (brs : List Tm) :
    Tm.size scrut < Tm.size (Tm.case I n scrut C brs) := by
  simp only [Tm.size]; omega

private theorem size_lt_case_motive (I n : Nat) (scrut C : Tm) (brs : List Tm) :
    Tm.size C < Tm.size (Tm.case I n scrut C brs) := by
  simp only [Tm.size]; omega

private theorem size_lt_case_mem {I n : Nat} {scrut C : Tm} {brs : List Tm} {a : Tm}
    (ha : a ∈ brs) : Tm.size a < Tm.size (Tm.case I n scrut C brs) := by
  have h := size_le_foldr brs a ha
  simp only [Tm.size]; omega

private theorem upRen_comp (f g : Nat → Nat) :
    (fun x => Tm.upRen f (Tm.upRen g x)) = Tm.upRen (fun x => f (g x)) := by
  funext x
  cases x with
  | zero => rfl
  | succ y => simp [Tm.upRen]

private theorem upRenN_succ (m : Nat) (f : Nat → Nat) :
    Tm.upRenN (m + 1) f = Tm.upRen (Tm.upRenN m f) := rfl

private theorem upRenN_comp (m : Nat) (f g : Nat → Nat) :
    (fun x => Tm.upRenN m f (Tm.upRenN m g x))
      = Tm.upRenN m (fun x => f (g x)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      funext x
      rw [upRenN_succ, upRenN_succ, upRenN_succ]
      rw [congrFun (upRen_comp (Tm.upRenN m f) (Tm.upRenN m g)) x, ih]

private theorem rename_comp (t : Tm) (f g : Nat → Nat) :
    Tm.rename f (Tm.rename g t) = Tm.rename (fun x => f (g x)) t := by
  revert f g t
  apply strong_induction
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
          ih C (size_lt_case_motive I n scrut C brs) (Tm.upRenN (n + 1) f) (Tm.upRenN (n + 1) g),
          upRenN_comp]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact ih a (size_lt_case_mem ha) f g

/-- A single shift at cutoff `0` is addition at every free variable. -/
private theorem shiftSub_add (d : Nat) : ∀ y : Nat, Tm.shiftSub d 0 y = y + d := by
  intro y
  simp [Tm.shiftSub]

/-- Two single shifts at cutoff `0` compose into one shift by the sum. -/
private theorem shiftSub_comp (d e : Nat) :
    (fun x => Tm.shiftSub d 0 (Tm.shiftSub e 0 x)) = Tm.shiftSub (d + e) 0 := by
  funext x
  rw [shiftSub_add e, shiftSub_add d, shiftSub_add (d + e)]
  omega

private theorem shift_shift (d e : Nat) (t : Tm) :
    Tm.shift d 0 (Tm.shift e 0 t) = Tm.shift (d + e) 0 t := by
  simp only [Tm.shift]
  rw [rename_comp, shiftSub_comp]

end Tm

/-! ## Insertion -/

namespace Ctx

/-- Insert the binder `B` at de Bruijn position `n` of the context `Γ`. -/
def insertAt (n : Nat) (B : Tm) (Γ : Ctx) : Ctx :=
  Γ.take n ++ [B] ++ Γ.drop n

@[simp] theorem insertAt_zero (B : Tm) (Γ : Ctx) :
    Ctx.insertAt 0 B Γ = B :: Γ := by
  simp [Ctx.insertAt]

@[simp] theorem insertAt_succ_cons (n : Nat) (B A : Tm) (Γ : Ctx) :
    Ctx.insertAt (n + 1) B (A :: Γ) = A :: Ctx.insertAt n B Γ := by
  simp [Ctx.insertAt]

end Ctx

/-! ## Lookup through an insertion -/

/-- Positions below the insertion are read exactly as before. -/
theorem ctxLookup_insertAt_lt (B : Tm) :
    ∀ (Γ : Ctx) (n x : Nat), x < n → x < Γ.length →
      ctxLookup (Ctx.insertAt n B Γ) x = ctxLookup Γ x
  | [], n, x, _, hΓ => by simp at hΓ
  | _ :: Γ, 0, x, hn, _ => by omega
  | A :: Γ, n + 1, 0, _, _ => by simp [Ctx.insertAt_succ_cons, ctxLookup]
  | A :: Γ, n + 1, x + 1, hn, hΓ => by
      simp only [Ctx.insertAt_succ_cons, ctxLookup]
      rw [ctxLookup_insertAt_lt B Γ n x (by omega) (by simpa using hΓ)]

/-- The inserted binder reads back shifted once for itself and once for every
binder above it. -/
theorem ctxLookup_insertAt_eq (B : Tm) :
    ∀ (Γ : Ctx) (n : Nat), n ≤ Γ.length →
      ctxLookup (Ctx.insertAt n B Γ) n = some (Tm.shift (n + 1) 0 B)
  | [], n, hn => by
      cases n with
      | zero => simp [Ctx.insertAt, ctxLookup]
      | succ n => simp at hn
  | A :: Γ, 0, _ => by simp [Ctx.insertAt, ctxLookup]
  | A :: Γ, n + 1, hn => by
      have hn' : n ≤ Γ.length := by simpa using hn
      have h : (some (Tm.shift (n + 1) 0 B)).map (Tm.shift 1 0)
          = some (Tm.shift (n + 1 + 1) 0 B) := by
        simp only [Option.map_some]
        rw [Tm.shift_shift]
        have hidx : (1 : Nat) + (n + 1) = n + 1 + 1 := by omega
        rw [hidx]
      simpa only [Ctx.insertAt_succ_cons, ctxLookup, ctxLookup_insertAt_eq B Γ n hn']
        using h

/-- Positions above the insertion move down by one, with one additional shift
for the inserted binder. -/
theorem ctxLookup_insertAt_gt (B : Tm) :
    ∀ (Γ : Ctx) (n x : Nat), n < x →
      ctxLookup (Ctx.insertAt n B Γ) x
        = (ctxLookup Γ (x - 1)).map (Tm.shift 1 0)
  | [], n, x, _ => by
      cases x with
      | zero => omega
      | succ x => simp [Ctx.insertAt, ctxLookup]
  | _ :: Γ, 0, x, _ => by
      cases x with
      | zero => omega
      | succ x => simp [Ctx.insertAt, ctxLookup]
  | _ :: Γ, n + 1, x, hx => by
      cases x with
      | zero => omega
      | succ x =>
          cases x with
          | zero => omega
          | succ y =>
              have h : ctxLookup (Ctx.insertAt n B Γ) (Nat.succ y)
                  = (ctxLookup Γ y).map (Tm.shift 1 0) := by
                simpa using ctxLookup_insertAt_gt B Γ n (Nat.succ y) (by omega)
              simp only [Ctx.insertAt_succ_cons, ctxLookup, h]
              simp [ctxLookup]

/-! ## The context constructors -/

/-- Insertion into the base context lands after the telescope `As`, since
`ctxExtendMany` prepends `As.length` binders. -/
theorem ctxExtendMany_insertAt (B : Tm) (j : Nat) (K : Ctx) :
    ∀ As : List Tm,
      ctxExtendMany (Ctx.insertAt j B K) As
        = Ctx.insertAt (As.length + j) B (ctxExtendMany K As)
  | [] => by simp [ctxExtendMany]
  | A :: As => by
      simp only [ctxExtendMany, ctxExtend]
      rw [← Ctx.insertAt_succ_cons (n := j) (B := B) (A := A) (Γ := K)]
      rw [ctxExtendMany_insertAt B (j + 1) (A :: K) (As.map (Tm.shift 1 0))]
      have hlen : (As.map (Tm.shift 1 0)).length + (j + 1) = (A :: As).length + j := by
        simp only [List.length_map, List.length_cons]
        omega
      rw [hlen]
termination_by As => As.length
decreasing_by simp_wf

/-- Prepending `B` to the base context inserts it after the telescope `As`. -/
theorem ctxExtendMany_insert (B : Tm) (Γ : Ctx) (As : List Tm) :
    ctxExtendMany (B :: Γ) As
      = Ctx.insertAt As.length B (ctxExtendMany Γ As) := by
  simpa using ctxExtendMany_insertAt B 0 Γ As

/-- The case motive context of an extended context is the extended motive
context with the fresh binder inserted after the index telescope. -/
theorem caseMotiveCtx_insert (B : Tm) (Γ : Ctx) (I : Nat) (sig : IndSig)
    (params : List Tm) :
    caseMotiveCtx (B :: Γ) I sig params
      = Ctx.insertAt (sig.indices.length + 1) B (caseMotiveCtx Γ I sig params) := by
  simp only [caseMotiveCtx, ctxExtend, ctxExtendMany_insert, List.length_map,
    Ctx.insertAt_succ_cons]

end Transport.Mltt
