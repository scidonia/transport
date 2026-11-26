import Transport.Mltt.Weaken

/-!
# Well-scoped terms and signatures

The existing indexed core stores signature types without a free-variable
bound.  General weakening therefore cannot commute renaming with `substMany`.
This file supplies the missing invariant:

* `WellScoped d t`: every free variable of `t` is below `d` (locally bound
  variables are handled by the depth).
* `rename_upRenN_of_wellScoped`: a well-scoped term is unchanged by the
  identity renaming below its depth.
* `WellFormedSig`: the proposed telescope invariant for an indexed signature.

The general weakening and substitution theorems are the next layer.
-/

namespace Transport.Mltt.Scoped

open Transport.Mltt
open Transport.Mltt.Weaken

/-- `WellScoped d t`: all free variables of `t` are below `d`, with the depth
increased under binders.  The `case` motive binds its indices and the
scrutinee. -/
inductive WellScoped : Nat → Tm → Prop
  | var {d x} : x < d → WellScoped d (.var x)
  | sort {d i} : WellScoped d (.sort i)
  | pi {d A B} : WellScoped d A → WellScoped (d + 1) B → WellScoped d (.pi A B)
  | lam {d A b} : WellScoped d A → WellScoped (d + 1) b → WellScoped d (.lam A b)
  | app {d f u} : WellScoped d f → WellScoped d u → WellScoped d (.app f u)
  | fix {d A b} : WellScoped d A → WellScoped (d + 1) b → WellScoped d (.fix A b)
  | ind {d I args} : (∀ a ∈ args, WellScoped d a) → WellScoped d (.ind I args)
  | roll {d I c args} : (∀ a ∈ args, WellScoped d a) → WellScoped d (.roll I c args)
  | case {d I n scrut C brs} :
      WellScoped d scrut →
      WellScoped (d + n + 1) C →
      (∀ b ∈ brs, WellScoped d b) →
      WellScoped d (.case I n scrut C brs)

/-- Composition of the identity renaming below a depth. -/
theorem upRenN_add (ρ : Nat → Nat) (a b : Nat) :
    Tm.upRenN a (Tm.upRenN b ρ) = Tm.upRenN (a + b) ρ := by
  funext x
  by_cases h : x < a + b
  · rw [upRenN_lt (a + b) ρ h]
    by_cases hx : x < a
    · rw [upRenN_lt a (Tm.upRenN b ρ) hx]
    · have hxa : a ≤ x := Nat.le_of_not_lt hx
      rw [upRenN_ge a (Tm.upRenN b ρ) hxa]
      have hxb : x - a < b := by omega
      rw [upRenN_lt b ρ hxb]
      omega
  · have hge : a + b ≤ x := Nat.le_of_not_lt h
    rw [upRenN_ge (a + b) ρ hge]
    have hxa : a ≤ x := by omega
    rw [upRenN_ge a (Tm.upRenN b ρ) hxa]
    have hxb : b ≤ x - a := by omega
    rw [upRenN_ge b ρ hxb]
    have hsub : x - a - b = x - (a + b) := by omega
    rw [hsub]
    omega

/-- `upRenN (d+1)` is `upRen` after `upRenN d`. -/
theorem upRenN_succ (ρ : Nat → Nat) (d : Nat) :
    Tm.upRenN (d + 1) ρ = Tm.upRen (Tm.upRenN d ρ) := by
  cases d with
  | zero => rfl
  | succ d => rfl

/-- A well-scoped term is fixed by the identity renaming below its depth. -/
theorem rename_upRenN_of_wellScoped {ρ : Nat → Nat} :
    ∀ (t : Tm) (d : Nat), WellScoped d t →
      Tm.rename (Tm.upRenN d ρ) t = t := by
  apply tm_strong_induction
  intro t ih d h
  cases t with
  | var x =>
      cases h with
      | var hx => simp [Tm.rename, upRenN_lt d ρ hx]
  | sort i =>
      simp [Tm.rename]
  | pi A B =>
      cases h with
      | pi hA hB =>
          simp only [Tm.rename]
          rw [ih A (size_lt_pi_left A B) d hA]
          rw [← upRenN_succ ρ d]
          rw [ih B (size_lt_pi_right A B) (d + 1) hB]
  | lam A b =>
      cases h with
      | lam hA hb =>
          simp only [Tm.rename]
          rw [ih A (size_lt_lam_left A b) d hA]
          rw [← upRenN_succ ρ d]
          rw [ih b (size_lt_lam_right A b) (d + 1) hb]
  | app f u =>
      cases h with
      | app hf hu =>
          simp only [Tm.rename]
          rw [ih f (size_lt_app_left f u) d hf]
          rw [ih u (size_lt_app_right f u) d hu]
  | fix A b =>
      cases h with
      | fix hA hb =>
          simp only [Tm.rename]
          rw [ih A (size_lt_fix_left A b) d hA]
          rw [← upRenN_succ ρ d]
          rw [ih b (size_lt_fix_right A b) (d + 1) hb]
  | ind I args =>
      cases h with
      | ind hargs =>
          simp only [Tm.rename]
          have hmap : args.map (Tm.rename (Tm.upRenN d ρ)) = args := by
            have hcongr := List.map_congr_left (l := args)
              (f := Tm.rename (Tm.upRenN d ρ)) (g := id)
              (fun a ha => by simpa using ih a (size_lt_ind_mem ha) d (hargs a ha))
            simpa using hcongr
          rw [hmap]
  | roll I c args =>
      cases h with
      | roll hargs =>
          simp only [Tm.rename]
          have hmap : args.map (Tm.rename (Tm.upRenN d ρ)) = args := by
            have hcongr := List.map_congr_left (l := args)
              (f := Tm.rename (Tm.upRenN d ρ)) (g := id)
              (fun a ha => by simpa using ih a (size_lt_roll_mem ha) d (hargs a ha))
            simpa using hcongr
          rw [hmap]
  | case I n scrut C brs =>
      cases h with
      | case hscrut hC hbrs =>
          simp only [Tm.rename]
          rw [ih scrut (size_lt_case_scrut I n scrut C brs) d hscrut]
          rw [upRenN_add ρ (n + 1) d]
          have hidx : n + 1 + d = d + n + 1 := by omega
          rw [hidx]
          rw [ih C (size_lt_case_motive I n scrut C brs) (d + n + 1) hC]
          have hmap : brs.map (Tm.rename (Tm.upRenN d ρ)) = brs := by
            have hcongr := List.map_congr_left (l := brs)
              (f := Tm.rename (Tm.upRenN d ρ)) (g := id)
              (fun b hb => by simpa using ih b (size_lt_case_mem hb) d (hbrs b hb))
            simpa using hcongr
          rw [hmap]

/-- The proposed telescope invariant for an indexed signature.  The parameter
and index types are scoped by the parameter telescope; a constructor's
arguments are scoped by the full argument list. -/
def WellFormedSig (sig : IndSig) : Prop :=
  (∀ p ∈ sig.params, WellScoped sig.params.length p)
    ∧ (∀ i ∈ sig.indices, WellScoped sig.params.length i)
    ∧ ∀ ctor ∈ sig.ctors,
        (∀ p ∈ ctor.paramTys,
          WellScoped (sig.params.length + ctor.paramTys.length + ctor.recArgs.length) p)
          ∧ (∀ i ∈ ctor.indices, WellScoped sig.params.length i)
          ∧ ∀ idxs ∈ ctor.recArgs, ∀ t ∈ idxs,
              WellScoped (sig.params.length + ctor.paramTys.length + ctor.recArgs.length) t

/-- Every family in the environment satisfies the telescope invariant. -/
def WellFormedEnv (env : Env) : Prop :=
  ∀ (I : Nat) (sig : IndSig), lookupInd env I = some sig → WellFormedSig sig


/-- The `Eq` signature satisfies the telescope invariant. -/
theorem eq_sig_wellFormed : WellFormedSig Eq_sig := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp [Eq_sig] at hp
    rcases hp with rfl | rfl
    · exact WellScoped.sort
    · exact WellScoped.var (by simp [Eq_sig])
  · intro i hi
    simp [Eq_sig] at hi
    subst hi
    exact WellScoped.var (by simp [Eq_sig])
  · intro ctor hc
    simp [Eq_sig] at hc
    subst hc
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp at hp
    · intro i hi
      simp at hi
      subst hi
      exact WellScoped.var (by simp [Eq_sig])
    · intro idxs hidxs t ht
      simp at hidxs

/-- The environment used by the `Eq` typing theorem satisfies the invariant. -/
theorem wellFormedEnv_Eq : WellFormedEnv [Eq_sig] := by
  intro I sig h
  cases I with
  | zero =>
      simp [lookupInd, lookup] at h
      subst h
      exact eq_sig_wellFormed
  | succ I =>
      simp [lookupInd, lookup] at h

/-- Renaming commutes with `substMany` when the substituted term is scoped by
the substitution length. -/
theorem substMany_rename_of_wellScoped (ρ : Nat → Nat) (xs : List Tm) (t : Tm)
    (h : WellScoped xs.length t) :
    substMany (xs.map (Tm.rename ρ)) t = Tm.rename ρ (substMany xs t) := by
  rw [rename_substMany t ρ xs]
  rw [rename_upRenN_of_wellScoped (ρ := ρ) t xs.length h]

end Transport.Mltt.Scoped
