import Transport.Mltt.ContextInsert
import Transport.Mltt.Subst
import Transport.Mltt.Scoped

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-!
# Weakening a case-motive context by inserting a binder

`caseMotiveCtx_insert` says that `caseMotiveCtx (B :: Γ) …` is
`caseMotiveCtx Γ …` with `B` spliced in at position `sig.indices.length + 1`.
This file relates the two contexts by a `Wk` relation whose renaming skips that
inserted position:

    insertRen m k = if k < m + 1 then k else k + 1

Adding `B` at the front of `Γ` shifts every variable of `Γ` by one, so the
parameters of the case motive must be renamed by `Tm.shift 1 0` on the target
side; keeping them fixed is not provable (the stored motive is the same term on
both sides, while its variables into `Γ` have to move).

The only extra hypothesis is that the index types are scoped by the parameter
telescope: `∀ idx ∈ sig.indices, WellScoped params.length idx`.  It is what
lets renaming commute with the parameter substitution `substParams`.  In the
typing use `params = args.take sig.params.length`, so `params.length` is
`sig.params.length` and this is exactly the telescope invariant.
-/

namespace Transport.Mltt

/-! ## The insertion renaming -/

/-- The renaming induced by inserting a binder at position `m + 1`: variables
below the insertion are unchanged, variables at or above it move one place
up. -/
def insertRen (m : Nat) : Nat → Nat := fun k => if k < m + 1 then k else k + 1

theorem insertRen_of_lt {m k : Nat} (h : k < m + 1) : insertRen m k = k := by
  simp [insertRen, h]

theorem insertRen_of_ge {m k : Nat} (h : m + 1 ≤ k) : insertRen m k = k + 1 := by
  simp [insertRen, Nat.not_lt.mpr h]

/-! ## Shifting and renaming helpers -/

theorem shiftSub_one_zero (k : Nat) : Tm.shiftSub 1 0 k = k + 1 := by
  simp only [Tm.shiftSub]
  rw [if_neg (Nat.not_lt_zero k)]

theorem shiftSub_zero_eq (d k : Nat) : Tm.shiftSub d 0 k = k + d := by
  simp only [Tm.shiftSub]
  rw [if_neg (Nat.not_lt_zero k)]

theorem shift_zero (t : Tm) : Tm.shift 0 0 t = t := by
  simp only [Tm.shift]
  have h : Tm.shiftSub 0 0 = id := by
    funext k
    simp [Tm.shiftSub]
  rw [h, Subst.rename_id]

theorem shift_shift_local (d e : Nat) (t : Tm) :
    Tm.shift d 0 (Tm.shift e 0 t) = Tm.shift (d + e) 0 t := by
  simp only [Tm.shift]
  rw [Weaken.rename_comp]
  congr 1
  funext k
  rw [shiftSub_zero_eq e, shiftSub_zero_eq d, shiftSub_zero_eq (d + e)]
  omega

/-- A renaming that is `k + 1` at and above `a` commutes with a shift by `a`. -/
theorem rename_shift_of_ge {ρ : Nat → Nat} {a : Nat}
    (h : ∀ k, a ≤ k → ρ k = k + 1) (t : Tm) :
    Tm.rename ρ (Tm.shift a 0 t) = Tm.shift (a + 1) 0 t := by
  simp only [Tm.shift]
  rw [Weaken.rename_comp]
  congr 1
  funext k
  rw [shiftSub_zero_eq a, shiftSub_zero_eq (a + 1)]
  rw [h (k + a) (by omega)]
  omega

theorem option_map_map' {α β γ : Type} (f : β → γ) (g : α → β) (o : Option α) :
    Option.map f (Option.map g o) = Option.map (fun x => f (g x)) o := by
  cases o <;> rfl

theorem option_map_shift_zero (o : Option Tm) : Option.map (Tm.shift 0 0) o = o := by
  cases o with
  | none => rfl
  | some t => simp [shift_zero]

/-! ## Looking up the telescope

`ctxLookup` shifts a stored term once for every binder above it, so a lookup in
`ctxExtendMany Γ As` is either `As`'s element at the mirrored position, shifted
by `As.length`, or a lookup in `Γ` shifted by `As.length`. -/

private theorem ctxLookup_ctxExtendMany_aux :
    ∀ n, ∀ (Γ : Ctx) (As : List Tm), As.length = n → ∀ j,
      (j < As.length → ctxLookup (ctxExtendMany Γ As) j
        = (As[As.length - 1 - j]?).map (Tm.shift As.length 0)) ∧
      (As.length ≤ j → ctxLookup (ctxExtendMany Γ As) j
        = (ctxLookup Γ (j - As.length)).map (Tm.shift As.length 0)) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro Γ As hlen j
    cases As with
    | nil =>
        refine ⟨?_, ?_⟩
        · intro h
          simp at h
        · intro _
          rw [ctxExtendMany.eq_1]
          simp only [List.length_nil, Nat.sub_zero]
          exact (option_map_shift_zero (ctxLookup Γ j)).symm
    | cons A As =>
        have hctx : ctxExtendMany Γ (A :: As)
            = ctxExtendMany (A :: Γ) (As.map (Tm.shift 1 0)) := by
          rw [ctxExtendMany.eq_2]
          rfl
        have hlt : (As.map (Tm.shift 1 0)).length < n := by
          have h : (A :: As).length = n := hlen
          simp only [List.length_cons, List.length_map] at h ⊢
          omega
        have ihAs1 := ih (As.map (Tm.shift 1 0)).length hlt (A :: Γ)
          (As.map (Tm.shift 1 0)) rfl
        refine ⟨?_, ?_⟩
        · intro hj
          rw [hctx]
          by_cases hjm : j < As.length
          · have hjm' : j < (As.map (Tm.shift 1 0)).length := by simpa using hjm
            rw [(ihAs1 j).1 hjm']
            simp only [List.length_map, List.length_cons]
            have hidx : As.length + 1 - 1 - j = (As.length - 1 - j) + 1 := by omega
            rw [hidx, List.getElem?_cons_succ, List.getElem?_map, option_map_map']
            congr 1
            funext t
            rw [shift_shift_local As.length 1 t]
          · have hje : j = As.length := by
              simp only [List.length_cons] at hj
              omega
            subst hje
            rw [(ihAs1 As.length).2 (by simp)]
            simp only [List.length_map, Nat.sub_self]
            have hidx : (A :: As).length - 1 - As.length = 0 := by
              simp only [List.length_cons]
              omega
            rw [hidx, List.getElem?_cons_zero]
            simp only [List.length_cons, ctxLookup, Option.map_some, Option.some.injEq]
            rw [shift_shift_local As.length 1 A]
        · intro hj
          simp only [List.length_cons] at hj
          rw [hctx]
          have hj1 : (As.map (Tm.shift 1 0)).length ≤ j := by
            simp only [List.length_map]
            omega
          rw [(ihAs1 j).2 hj1]
          simp only [List.length_map]
          have hk : j - As.length = (j - As.length - 1) + 1 := by omega
          rw [hk]
          simp only [ctxLookup]
          rw [option_map_map']
          have hidx : j - (A :: As).length = j - As.length - 1 := by
            simp only [List.length_cons]
            omega
          rw [hidx]
          simp only [List.length_cons]
          congr 1
          funext t
          rw [shift_shift_local As.length 1 t]

/-- The two lookup cases for `ctxExtendMany`. -/
theorem ctxLookup_ctxExtendMany (Γ : Ctx) (As : List Tm) (j : Nat) :
    (j < As.length → ctxLookup (ctxExtendMany Γ As) j
      = (As[As.length - 1 - j]?).map (Tm.shift As.length 0)) ∧
    (As.length ≤ j → ctxLookup (ctxExtendMany Γ As) j
      = (ctxLookup Γ (j - As.length)).map (Tm.shift As.length 0)) :=
  ctxLookup_ctxExtendMany_aux As.length Γ As rfl j

/-! ## The motive -/

/-- Renaming a parameter commutes with the two shifts in the case motive. -/
theorem rename_shift_shift (n : Nat) (t : Tm) :
    Tm.rename (insertRen n) (Tm.shift 1 0 (Tm.shift n 0 t))
      = Tm.shift 1 0 (Tm.shift n 0 (Tm.shift 1 0 t)) := by
  have h1 : Tm.shift 1 0 (Tm.shift n 0 t) = Tm.shift (n + 1) 0 t := by
    rw [shift_shift_local 1 n t]
    congr 1
    omega
  rw [h1, rename_shift_of_ge (a := n + 1) (by intro k hk; exact insertRen_of_ge hk)]
  have h2 : Tm.shift n 0 (Tm.shift 1 0 t) = Tm.shift (n + 1) 0 t := by
    rw [shift_shift_local n 1 t]
  rw [h2, shift_shift_local 1 (n + 1) t]
  congr 1 <;> omega

/-- The case motive, viewed from position `0`, commutes with the insertion
renaming when the parameters are shifted by one. -/
theorem motive_rename_shift (I n : Nat) (params : List Tm) :
    Tm.rename (insertRen n)
      (Tm.shift 1 0
        (Tm.ind I (params.map (Tm.shift n 0) ++ (List.range n).reverse.map Tm.var)))
      = Tm.shift 1 0
        (Tm.ind I ((params.map (Tm.shift 1 0)).map (Tm.shift n 0)
          ++ (List.range n).reverse.map Tm.var)) := by
  simp only [Tm.shift, Tm.rename, List.map_append, List.map_map]
  congr 1
  have h1 : List.map (Tm.rename (insertRen n) ∘ Tm.rename (Tm.shiftSub 1 0)
        ∘ Tm.shift n 0) params
      = List.map (Tm.rename (Tm.shiftSub 1 0) ∘ Tm.shift n 0
        ∘ Tm.shift 1 0) params := by
    apply List.map_congr_left
    intro p _
    simpa only [Function.comp_apply, Tm.shift] using rename_shift_shift n p
  have h2 : List.map (Tm.rename (insertRen n) ∘ Tm.rename (Tm.shiftSub 1 0)
        ∘ Tm.var) (List.range n).reverse
      = List.map (Tm.rename (Tm.shiftSub 1 0) ∘ Tm.var)
          (List.range n).reverse := by
    apply List.map_congr_left
    intro j hj
    simp only [Function.comp_apply, Tm.rename]
    rw [shiftSub_one_zero]
    rw [insertRen_of_lt (by simp only [List.mem_reverse, List.mem_range] at hj; omega)]
  rw [h1, h2]

/-! ## Lookups of a case-motive context -/

theorem caseMotiveCtx_lookup_succ (Γ : Ctx) (I : Nat) (sig : IndSig)
    (params : List Tm) (j : Nat) (hj : j < sig.indices.length) :
    ctxLookup (caseMotiveCtx Γ I sig params) (j + 1)
      = ((sig.indices.map (substParams params))[sig.indices.length - 1 - j]?).map
          (Tm.shift (sig.indices.length + 1) 0) := by
  have hctx : caseMotiveCtx Γ I sig params
      = ctxExtend (ctxExtendMany Γ (sig.indices.map (substParams params)))
          (Tm.ind I (params.map (Tm.shift sig.indices.length 0)
            ++ (List.range sig.indices.length).reverse.map Tm.var)) := rfl
  rw [hctx]
  change (ctxLookup (ctxExtendMany Γ (sig.indices.map (substParams params))) j).map
      (Tm.shift 1 0)
    = ((sig.indices.map (substParams params))[sig.indices.length - 1 - j]?).map
        (Tm.shift (sig.indices.length + 1) 0)
  have hj' : j < (sig.indices.map (substParams params)).length := by simpa using hj
  rw [(ctxLookup_ctxExtendMany Γ (sig.indices.map (substParams params)) j).1 hj']
  simp only [List.length_map]
  rw [option_map_map']
  congr 1
  funext t
  rw [shift_shift_local 1 (sig.indices.length) t]
  congr 1 <;> omega

theorem caseMotiveCtx_lookup_ge (Γ : Ctx) (I : Nat) (sig : IndSig)
    (params : List Tm) (j : Nat) :
    ctxLookup (caseMotiveCtx Γ I sig params) (sig.indices.length + 1 + j)
      = (ctxLookup Γ j).map (Tm.shift (sig.indices.length + 1) 0) := by
  have hctx : caseMotiveCtx Γ I sig params
      = ctxExtend (ctxExtendMany Γ (sig.indices.map (substParams params)))
          (Tm.ind I (params.map (Tm.shift sig.indices.length 0)
            ++ (List.range sig.indices.length).reverse.map Tm.var)) := rfl
  rw [hctx]
  have hidx : sig.indices.length + 1 + j = (sig.indices.length + j) + 1 := by omega
  rw [hidx]
  change (ctxLookup (ctxExtendMany Γ (sig.indices.map (substParams params)))
      (sig.indices.length + j)).map (Tm.shift 1 0)
    = (ctxLookup Γ j).map (Tm.shift (sig.indices.length + 1) 0)
  have hlen : (sig.indices.map (substParams params)).length = sig.indices.length := by
    simp
  have hge : (sig.indices.map (substParams params)).length ≤ sig.indices.length + j := by
    rw [hlen]
    omega
  rw [(ctxLookup_ctxExtendMany Γ (sig.indices.map (substParams params))
        (sig.indices.length + j)).2 hge]
  simp only [hlen]
  have hsub : sig.indices.length + j - sig.indices.length = j := by omega
  rw [hsub, option_map_map']
  congr 1
  funext t
  rw [shift_shift_local 1 (sig.indices.length) t]
  congr 1 <;> omega

/-! ## Insertion lookup, without a length premise -/

/-- Positions below an insertion read back unchanged, provided the source
lookup is present (so the source is long enough). -/
theorem ctxLookup_insertAt_lt_of_lookup (B : Tm) :
    ∀ (Γ : Ctx) (n x : Nat) (A : Tm), x < n → ctxLookup Γ x = some A →
      ctxLookup (Ctx.insertAt n B Γ) x = some A
  | [], _, _, _, _, h => by simp [ctxLookup] at h
  | _ :: _, 0, _, _, _, _ => by omega
  | _ :: Γ, n + 1, 0, _, _, hx => by
      simp only [Ctx.insertAt_succ_cons, ctxLookup] at hx ⊢
      exact hx
  | A0 :: Γ, n + 1, x + 1, A, hx, hxlookup => by
      simp only [Ctx.insertAt_succ_cons, ctxLookup] at hxlookup ⊢
      cases hb : ctxLookup Γ x with
      | none => simp [hb] at hxlookup
      | some A0' =>
          have hlookup : Tm.shift 1 0 A0' = A := by
            rw [hb] at hxlookup
            exact Option.some.inj hxlookup
          have hrec := ctxLookup_insertAt_lt_of_lookup B Γ n x A0' (by omega) hb
          rw [hrec]
          simp only [Option.map_some, Option.some.injEq]
          exact hlookup

/-! ## Parameter substitution under the shift -/

theorem substParams_shift (idx : Tm) {params : List Tm}
    (h : Scoped.WellScoped params.length idx) :
    substParams (params.map (Tm.shift 1 0)) idx = Tm.shift 1 0 (substParams params idx) := by
  unfold substParams
  rw [← List.map_reverse]
  change substMany (params.reverse.map (Tm.rename (Tm.shiftSub 1 0))) idx
    = Tm.rename (Tm.shiftSub 1 0) (substMany params.reverse idx)
  exact Scoped.substMany_rename_of_wellScoped (Tm.shiftSub 1 0) params.reverse idx
    (by simpa using h)

/-! ## The main statement -/

/-- Weakening of the case-motive context when `B` is prepended to `Γ`.  The
renaming is `insertRen sig.indices.length`; the parameters on the target side
are shifted by one, matching `B`'s position at the front of `Γ`. -/
theorem caseMotiveCtx_wk_insert (B : Tm) (Γ : Ctx) (I : Nat) (sig : IndSig)
    (params : List Tm)
    (hsig : ∀ idx ∈ sig.indices, Scoped.WellScoped params.length idx) :
    Weaken.Wk (insertRen sig.indices.length)
      (caseMotiveCtx Γ I sig params)
      (caseMotiveCtx (B :: Γ) I sig (params.map (Tm.shift 1 0))) := by
  intro x A hx
  rw [caseMotiveCtx_insert]
  have hAs' : sig.indices.map (substParams (params.map (Tm.shift 1 0)))
      = (sig.indices.map (substParams params)).map (Tm.shift 1 0) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro idx hidx
    exact substParams_shift idx (hsig idx hidx)
  by_cases hxlt : x < sig.indices.length + 1
  · have hρ : insertRen (sig.indices.length) x = x := insertRen_of_lt hxlt
    rw [hρ]
    have hS' : ctxLookup (caseMotiveCtx Γ I sig (params.map (Tm.shift 1 0))) x
        = some (Tm.rename (insertRen (sig.indices.length)) A) := by
      cases x with
      | zero =>
          have hM0 : ctxLookup (caseMotiveCtx Γ I sig params) 0
              = some (Tm.shift 1 0 (Tm.ind I
                  (params.map (Tm.shift (sig.indices.length) 0)
                    ++ (List.range (sig.indices.length)).reverse.map Tm.var))) := rfl
          have hA : A = Tm.shift 1 0 (Tm.ind I
              (params.map (Tm.shift (sig.indices.length) 0)
                ++ (List.range (sig.indices.length)).reverse.map Tm.var)) := by
            rw [hM0] at hx
            exact (Option.some.inj hx).symm
          have hM'0 : ctxLookup (caseMotiveCtx Γ I sig (params.map (Tm.shift 1 0))) 0
              = some (Tm.shift 1 0 (Tm.ind I
                  ((params.map (Tm.shift 1 0)).map (Tm.shift (sig.indices.length) 0)
                    ++ (List.range (sig.indices.length)).reverse.map Tm.var))) := rfl
          rw [hM'0, hA, motive_rename_shift I (sig.indices.length) params]
      | succ j =>
          have hj : j < sig.indices.length := by omega
          rw [caseMotiveCtx_lookup_succ Γ I sig params j hj] at hx
          cases hget : (sig.indices.map (substParams params))[sig.indices.length - 1 - j]? with
          | none => simp [hget] at hx
          | some T =>
              have hA : A = Tm.shift (sig.indices.length + 1) 0 T := by
                rw [hget] at hx
                exact (Option.some.inj hx).symm
              rw [hA, caseMotiveCtx_lookup_succ Γ I sig (params.map (Tm.shift 1 0)) j hj,
                  hAs', List.getElem?_map, hget]
              simp only [Option.map_some, Option.some.injEq]
              rw [rename_shift_of_ge (a := sig.indices.length + 1)
                    (by intro k hk; exact insertRen_of_ge hk)]
              rw [shift_shift_local (sig.indices.length + 1) 1 T]
    exact ctxLookup_insertAt_lt_of_lookup B _ (sig.indices.length + 1) x
      (Tm.rename (insertRen (sig.indices.length)) A) hxlt hS'
  · have hxge : sig.indices.length + 1 ≤ x := Nat.le_of_not_lt hxlt
    have hρ : insertRen (sig.indices.length) x = x + 1 := insertRen_of_ge hxge
    rw [hρ]
    rw [ctxLookup_insertAt_gt B _ (sig.indices.length + 1) (x + 1) (by omega)]
    simp only [Nat.add_sub_cancel]
    have hxS : ctxLookup (caseMotiveCtx Γ I sig params) x
        = (ctxLookup Γ (x - (sig.indices.length + 1))).map
            (Tm.shift (sig.indices.length + 1) 0) := by
      have h := caseMotiveCtx_lookup_ge Γ I sig params (x - (sig.indices.length + 1))
      rwa [show sig.indices.length + 1 + (x - (sig.indices.length + 1)) = x from by omega] at h
    have hxS' : ctxLookup (caseMotiveCtx Γ I sig (params.map (Tm.shift 1 0))) x
        = (ctxLookup Γ (x - (sig.indices.length + 1))).map
            (Tm.shift (sig.indices.length + 1) 0) := by
      have h := caseMotiveCtx_lookup_ge Γ I sig (params.map (Tm.shift 1 0))
        (x - (sig.indices.length + 1))
      rwa [show sig.indices.length + 1 + (x - (sig.indices.length + 1)) = x from by omega] at h
    rw [hxS']
    rw [hxS] at hx
    cases hg : ctxLookup Γ (x - (sig.indices.length + 1)) with
    | none => simp [hg] at hx
    | some t =>
        have hA : A = Tm.shift (sig.indices.length + 1) 0 t := by
          rw [hg] at hx
          exact (Option.some.inj hx).symm
        rw [hA]
        simp only [Option.map_some, Option.some.injEq]
        rw [rename_shift_of_ge (a := sig.indices.length + 1)
              (by intro k hk; exact insertRen_of_ge hk)]
        rw [shift_shift_local 1 (sig.indices.length + 1) t]
        congr 1 <;> omega

end Transport.Mltt
