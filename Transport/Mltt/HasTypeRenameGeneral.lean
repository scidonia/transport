import Transport.Mltt.ScopedSubst

/-!
# Renaming for the old indexed typing judgment

`HasType` keeps the parameter-only constructor result-index convention, and its
`case` rule places the motive under the family indices and the scrutinee.
Renaming a derivation under an arbitrary renamer `ρ` needs the environment to
carry the telescope invariant `WellFormedSig` and, for the `case` branches, the
constructor result-index arity that the branch obligations assume: a family's
constructor returns the family at the family's own index count.
-/

namespace Transport.Mltt

open Transport.Mltt.Scoped
open Transport.Mltt.Weaken

/-! ### The strict gate and the signature invariants -/

theorem lookupInd_of_lookupIndStrict {env : Env} {I : Nat} {sig : IndSig}
    (h : lookupIndStrict env I = some sig) : lookupInd env I = some sig := by
  cases hl : lookupInd env I with
  | none => simp [lookupIndStrict, hl] at h
  | some sig' =>
      by_cases hp : strictlyPositive I sig' = true
      · have hs : sig' = sig := by simpa [lookupIndStrict, hl, hp] using h
        rw [hs]
      · simp [lookupIndStrict, hl, hp] at h

/-- A constructor of a family returns that family at the family's index arity. -/
def SigIndexArity (sig : IndSig) : Prop :=
  ∀ (c : Nat) (ctor : CtorSig), lookupCtor sig c = some ctor →
    ctor.indices.length = sig.indices.length

/-- Every family in the environment has uniform constructor result-index
arity. -/
def EnvIndexArity (env : Env) : Prop :=
  ∀ (I : Nat) (sig : IndSig), lookupInd env I = some sig → SigIndexArity sig

theorem mem_ctors_of_lookupCtor {sig : IndSig} {c : Nat} {ctor : CtorSig}
    (h : lookupCtor sig c = some ctor) : ctor ∈ sig.ctors := by
  unfold lookupCtor lookup at h
  cases hc : sig.ctors[c]? with
  | none => simp [hc] at h
  | some x =>
      simp [hc] at h
      subst h
      exact List.mem_iff_getElem?.mpr ⟨c, hc⟩

theorem wellFormedSig_ctor {sig : IndSig} (h : WellFormedSig sig) {c : Nat}
    {ctor : CtorSig} (hc : lookupCtor sig c = some ctor) :
    (∀ p ∈ ctor.paramTys,
        WellScoped (sig.params.length + ctor.paramTys.length + ctor.recArgs.length) p)
      ∧ (∀ i ∈ ctor.indices, WellScoped sig.params.length i)
      ∧ (∀ idxs ∈ ctor.recArgs, ∀ t ∈ idxs,
          WellScoped (sig.params.length + ctor.paramTys.length + ctor.recArgs.length) t) :=
  h.2.2 ctor (mem_ctors_of_lookupCtor hc)

/-! ### Substitution under the parameter telescope -/

theorem substParams_rename_of_wellScoped (ρ : Nat → Nat) (xs : List Tm) (t : Tm)
    (h : WellScoped xs.length t) :
    substParams (List.map (Tm.rename ρ) xs) t = Tm.rename ρ (substParams xs t) := by
  unfold substParams
  rw [← List.map_reverse]
  exact substMany_rename_of_wellScoped ρ xs.reverse t (by simpa using h)

/-! ### Length induction -/

theorem list_length_induction {P : List Tm → Prop}
    (step : ∀ As, (∀ Bs, Bs.length < As.length → P Bs) → P As) : ∀ As, P As := by
  have key : ∀ n, ∀ As : List Tm, As.length = n → P As := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro As _
      apply step As
      intro Bs hBs
      exact ih Bs.length (by omega) Bs rfl
  intro As
  exact key As.length As rfl

/-! ### Renaming a prepended telescope of context binders -/

theorem upRenN_upRen (d : Nat) (ρ : Nat → Nat) :
    Tm.upRenN d (Tm.upRen ρ) = Tm.upRenN (d + 1) ρ := by
  show Tm.upRenN d (Tm.upRenN 1 ρ) = Tm.upRenN (d + 1) ρ
  exact upRenN_add ρ d 1

theorem ctxExtendMany_wk (As : List Tm) :
    ∀ {ρ : Nat → Nat} {Γ Δ : Ctx}, Wk ρ Γ Δ →
      Wk (Tm.upRenN As.length ρ) (ctxExtendMany Γ As)
        (ctxExtendMany Δ (List.map (Tm.rename ρ) As)) := by
  induction As using list_length_induction with
  | _ As ih =>
    intro ρ Γ Δ h
    cases As with
    | nil => simpa [ctxExtendMany, Tm.upRenN] using h
    | cons A As =>
      simp only [ctxExtendMany, ctxExtend, List.map_cons, List.length_cons]
      have hlist : List.map (Tm.rename (Tm.upRen ρ)) (List.map (Tm.shift 1 0) As)
          = List.map (Tm.shift 1 0) (List.map (Tm.rename ρ) As) := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro a _
        simpa [Tm.upRenN] using rename_upRenN_shift 0 ρ a
      rw [← hlist]
      have hm : List.length (List.map (Tm.shift 1 0) As) < List.length (A :: As) := by simp
      have hIH := ih (List.map (Tm.shift 1 0) As) hm
        (ρ := Tm.upRen ρ) (Γ := A :: Γ) (Δ := Tm.rename ρ A :: Δ) (Wk_extend h A)
      simp only [List.length_map] at hIH
      rw [upRenN_upRen] at hIH
      exact hIH

/-! ### The case-motive context -/

theorem caseScrutType_gen_rename (ρ : Nat → Nat) (I n : Nat) (params : List Tm) :
    Tm.rename (Tm.upRenN n ρ)
        (.ind I (List.map (Tm.shift n 0) params ++
          List.map Tm.var (List.reverse (List.range n))))
      = .ind I (List.map (Tm.shift n 0) (List.map (Tm.rename ρ) params) ++
          List.map Tm.var (List.reverse (List.range n))) := by
  simp only [Tm.rename, List.map_append, List.map_map]
  have h1 : List.map (Tm.rename (Tm.upRenN n ρ) ∘ Tm.shift n 0) params
      = List.map (Tm.shift n 0 ∘ Tm.rename ρ) params := by
    apply List.map_congr_left
    intro p _
    exact rename_upRenN_shift_ge n ρ p
  have h2 : List.map (Tm.rename (Tm.upRenN n ρ) ∘ Tm.var) (List.reverse (List.range n))
      = List.map Tm.var (List.reverse (List.range n)) := by
    apply List.map_congr_left
    intro j hj
    have hj' : j < n := by simpa using hj
    simp [Tm.rename, upRenN_lt n ρ hj']
  rw [h1, h2]

theorem caseMotiveCtx_wk_gen {ρ : Nat → Nat} {Γ Δ : Ctx} (h : Wk ρ Γ Δ)
    (I : Nat) (sig : IndSig) (params : List Tm)
    (hidx : List.map (substParams (List.map (Tm.rename ρ) params)) sig.indices
      = List.map (Tm.rename ρ) (List.map (substParams params) sig.indices)) :
    Wk (Tm.upRenN (sig.indices.length + 1) ρ) (caseMotiveCtx Γ I sig params)
      (caseMotiveCtx Δ I sig (List.map (Tm.rename ρ) params)) := by
  dsimp only [caseMotiveCtx]
  have hIdx := ctxExtendMany_wk (List.map (substParams params) sig.indices) h
  rw [List.length_map] at hIdx
  rw [← hidx] at hIdx
  have hfam := caseScrutType_gen_rename ρ I sig.indices.length params
  rw [← hfam]
  exact Wk_extend hIdx _

/-! ### Renaming the signature telescopes -/

theorem sigParams_rename (sig : IndSig) (h : WellFormedSig sig) (args : List Tm)
    (hlen : sig.params.length ≤ args.length) (ρ : Nat → Nat) :
    List.map (substMany (List.map (Tm.rename ρ) args)) sig.params
      = List.map (Tm.rename ρ) (List.map (substMany args) sig.params) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro p hp
  exact substMany_rename_of_wellScoped ρ args p ((h.1 p hp).mono hlen)

theorem sigIndices_rename (sig : IndSig) (h : WellFormedSig sig) (args : List Tm)
    (hlen : sig.params.length ≤ args.length) (ρ : Nat → Nat) :
    List.map (substParams (List.take sig.params.length (List.map (Tm.rename ρ) args)))
        sig.indices
      = List.map (Tm.rename ρ)
          (List.map (substParams (List.take sig.params.length args)) sig.indices) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro d hd
  have htake : (List.take sig.params.length args).length = sig.params.length := by
    rw [List.length_take, Nat.min_eq_left hlen]
  rw [← List.map_take]
  exact substParams_rename_of_wellScoped ρ (List.take sig.params.length args) d (by
    rw [htake]
    exact h.2.1 d hd)

theorem ctorParams_rename {sig : IndSig} (h : WellFormedSig sig) {c : Nat}
    {ctor : CtorSig} (hc : lookupCtor sig c = some ctor) (args : List Tm)
    (hlen : args.length = sig.params.length + ctor.paramTys.length + ctor.recArgs.length)
    (ρ : Nat → Nat) :
    List.map (substMany (List.map (Tm.rename ρ) args)) ctor.paramTys
      = List.map (Tm.rename ρ) (List.map (substMany args) ctor.paramTys) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro p hp
  exact substMany_rename_of_wellScoped ρ args p
    (((wellFormedSig_ctor h hc).1 p hp).mono (by omega))

theorem ctorIndices_rename {sig : IndSig} (h : WellFormedSig sig) {c : Nat}
    {ctor : CtorSig} (hc : lookupCtor sig c = some ctor) (args : List Tm)
    (hlen : sig.params.length ≤ args.length) (ρ : Nat → Nat) :
    List.map (substParams (List.take sig.params.length (List.map (Tm.rename ρ) args)))
        ctor.indices
      = List.map (Tm.rename ρ)
          (List.map (substParams (List.take sig.params.length args)) ctor.indices) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro d hd
  have htake : (List.take sig.params.length args).length = sig.params.length := by
    rw [List.length_take, Nat.min_eq_left hlen]
  rw [← List.map_take]
  exact substParams_rename_of_wellScoped ρ (List.take sig.params.length args) d (by
    rw [htake]
    exact (wellFormedSig_ctor h hc).2.1 d hd)

/-! ### General renaming -/

theorem hasType_rename_general {env : Env} {Γ Δ : Ctx} {ρ : Nat → Nat}
    (hEnv : WellFormedEnv env) (hArity : EnvIndexArity env) (hwk : Wk ρ Γ Δ)
    {t A : Tm} (h : HasType env Γ t A) :
    HasType env Δ (Tm.rename ρ t) (Tm.rename ρ A) := by
  have key : ∀ {Γ : Ctx} {t A : Tm}, HasType env Γ t A →
      ∀ (ρ : Nat → Nat) (Δ : Ctx), Wk ρ Γ Δ →
        HasType env Δ (Tm.rename ρ t) (Tm.rename ρ A) := by
    intro Γ t A h
    induction h with
    | var Γ x A hx =>
        intro ρ Δ hwk
        simp only [Tm.rename]
        exact HasType.var Δ (ρ x) (Tm.rename ρ A) (hwk x A hx)
    | sort Γ i =>
        intro ρ Δ _
        simpa [Tm.rename] using HasType.sort (env := env) Δ i
    | pi Γ A B i j hA hB ihA ihB =>
        intro ρ Δ hwk
        simp only [Tm.rename]
        have h1 : HasType env Δ (Tm.rename ρ A) (.sort i) := by
          simpa [Tm.rename] using ihA ρ Δ hwk
        have h2 : HasType env (Tm.rename ρ A :: Δ) (Tm.rename (Tm.upRen ρ) B)
            (.sort j) := by
          simpa [Tm.rename] using ihB (Tm.upRen ρ) (Tm.rename ρ A :: Δ) (Wk_extend hwk A)
        exact HasType.pi Δ (Tm.rename ρ A) (Tm.rename (Tm.upRen ρ) B) i j h1 h2
    | lam Γ A t B i hA ht ihA iht =>
        intro ρ Δ hwk
        simp only [Tm.rename]
        have h1 : HasType env Δ (Tm.rename ρ A) (.sort i) := by
          simpa [Tm.rename] using ihA ρ Δ hwk
        have h2 : HasType env (Tm.rename ρ A :: Δ) (Tm.rename (Tm.upRen ρ) t)
            (Tm.rename (Tm.upRen ρ) B) := by
          simpa [Tm.rename] using iht (Tm.upRen ρ) (Tm.rename ρ A :: Δ) (Wk_extend hwk A)
        exact HasType.lam Δ (Tm.rename ρ A) (Tm.rename (Tm.upRen ρ) t)
          (Tm.rename (Tm.upRen ρ) B) i h1 h2
    | app Γ t u A B ht hu iht ihu =>
        intro ρ Δ hwk
        simp only [Tm.rename]
        have h1 : HasType env Δ (Tm.rename ρ t)
            (.pi (Tm.rename ρ A) (Tm.rename (Tm.upRen ρ) B)) := by
          simpa [Tm.rename] using iht ρ Δ hwk
        have h2 : HasType env Δ (Tm.rename ρ u) (Tm.rename ρ A) := by
          simpa [Tm.rename] using ihu ρ Δ hwk
        have h := HasType.app Δ (Tm.rename ρ t) (Tm.rename ρ u)
          (Tm.rename ρ A) (Tm.rename (Tm.upRen ρ) B) h1 h2
        rw [subst0_eq_substMany] at h
        rw [subst0_eq_substMany, rename_substMany]
        simpa [Tm.upRenN] using h
    | ind Γ I sig args hsig hlen hargs ihargs =>
        intro ρ Δ hwk
        simp only [Tm.rename]
        have hwf : WellFormedSig sig := hEnv I sig (lookupInd_of_lookupIndStrict hsig)
        have hparams := sigParams_rename sig hwf args (by omega) ρ
        have hidxs := sigIndices_rename sig hwf args (by omega) ρ
        have hsplit :
            List.map (substMany (List.map (Tm.rename ρ) args)) sig.params ++
              List.map (substParams (List.take sig.params.length
                (List.map (Tm.rename ρ) args))) sig.indices
            = List.map (Tm.rename ρ)
                (List.map (substMany args) sig.params ++
                  List.map (substParams (List.take sig.params.length args)) sig.indices) := by
          rw [List.map_append, hparams, hidxs]
        refine HasType.ind Δ I sig (List.map (Tm.rename ρ) args) hsig ?_ ?_
        · simp only [List.length_map]; omega
        · intro i a A ha hA
          rw [hsplit, List.getElem?_map] at hA
          rw [List.getElem?_map] at ha
          cases harg : args[i]? with
          | none => simp [harg] at ha
          | some a0 =>
              simp [harg] at ha
              cases htyp : (List.map (substMany args) sig.params ++
                  List.map (substParams (List.take sig.params.length args)) sig.indices)[i]? with
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
        have hwf : WellFormedSig sig := hEnv I sig (lookupInd_of_lookupIndStrict hsig)
        have hlen' : List.length (List.map (Tm.rename ρ) args) =
            sig.params.length + ctor.paramTys.length + ctor.recArgs.length := by
          simp only [List.length_map]; omega
        have hidxeq :
            List.map (Tm.rename ρ)
                (List.take sig.params.length args ++
                  List.map (substParams (List.take sig.params.length args)) ctor.indices)
              = List.take sig.params.length (List.map (Tm.rename ρ) args) ++
                  List.map (substParams (List.take sig.params.length
                    (List.map (Tm.rename ρ) args))) ctor.indices := by
          rw [List.map_append, List.map_take]
          congr 1
          exact (ctorIndices_rename hwf hctor args (by omega) ρ).symm
        rw [hidxeq]
        refine HasType.roll Δ I sig c ctor (List.map (Tm.rename ρ) args) hsig hctor hlen' ?_ ?_ ?_
        · intro i a A ha hA
          have hpEq := sigParams_rename sig hwf args (by omega) ρ
          rw [hpEq, List.getElem?_map] at hA
          rw [← List.map_take, List.getElem?_map] at ha
          cases harg : (List.take sig.params.length args)[i]? with
          | none => rw [harg] at ha; simp at ha
          | some a0 =>
              rw [harg] at ha
              simp only [Option.map_some, Option.some.injEq] at ha
              cases htyp : (List.map (substMany args) sig.params)[i]? with
              | none => rw [htyp] at hA; simp at hA
              | some A0 =>
                  rw [htyp] at hA
                  simp only [Option.map_some, Option.some.injEq] at hA
                  have h1 := ihparams i a0 A0 harg htyp ρ Δ hwk
                  rw [ha] at h1
                  rw [hA] at h1
                  exact h1
        · intro i a A ha hA
          have htEq := ctorParams_rename hwf hctor args hlen ρ
          rw [htEq, List.getElem?_map] at hA
          rw [← List.map_drop, ← List.map_take, List.getElem?_map] at ha
          cases harg : (List.take ctor.paramTys.length (List.drop sig.params.length args))[i]? with
          | none => rw [harg] at ha; simp at ha
          | some a0 =>
              rw [harg] at ha
              simp only [Option.map_some, Option.some.injEq] at ha
              cases htyp : (List.map (substMany args) ctor.paramTys)[i]? with
              | none => rw [htyp] at hA; simp at hA
              | some A0 =>
                  rw [htyp] at hA
                  simp only [Option.map_some, Option.some.injEq] at hA
                  have h1 := ihctys i a0 A0 harg htyp ρ Δ hwk
                  rw [ha] at h1
                  rw [hA] at h1
                  exact h1
        · intro i r idxs hr hidx
          rw [← List.map_drop, ← List.map_drop, List.getElem?_map] at hr
          cases harg : (List.drop ctor.paramTys.length
              (List.drop sig.params.length args))[i]? with
          | none => rw [harg] at hr; simp at hr
          | some r0 =>
              rw [harg] at hr
              simp only [Option.map_some, Option.some.injEq] at hr
              have h1 := ihrec i r0 idxs harg hidx ρ Δ hwk
              have hidxMap :
                  List.map (Tm.rename ρ)
                      (List.take sig.params.length args ++
                        List.map (substMany args) idxs)
                    = List.take sig.params.length (List.map (Tm.rename ρ) args) ++
                        List.map (substMany (List.map (Tm.rename ρ) args)) idxs := by
                rw [List.map_append, List.map_take, List.map_map]
                congr 1
                apply List.map_congr_left
                intro t ht
                exact (substMany_rename_of_wellScoped ρ args t
                  (((wellFormedSig_ctor hwf hctor).2.2 idxs
                    (List.mem_iff_getElem?.mpr ⟨i, hidx⟩) t ht).mono (by omega))).symm
              have h1' : HasType env Δ (Tm.rename ρ r0)
                  (.ind I (List.take sig.params.length (List.map (Tm.rename ρ) args) ++
                    List.map (substMany (List.map (Tm.rename ρ) args)) idxs)) := by
                simpa [Tm.rename, hidxMap] using h1
              rw [hr] at h1'
              exact h1'
    | case Γ I n sig scrut C brs i args hsig hn hlen hscrut hmotive hbrs hbranch
        ihscrut ihmotive ihbranch =>
        intro ρ Δ hwk
        simp only [Tm.rename]
        have hwf : WellFormedSig sig := hEnv I sig (lookupInd_of_lookupIndStrict hsig)
        have hsigArity : SigIndexArity sig :=
          hArity I sig (lookupInd_of_lookupIndStrict hsig)
        have hlen' : List.length (List.map (Tm.rename ρ) args) =
            sig.params.length + sig.indices.length := by
          simp only [List.length_map]; omega
        have hscrut' : HasType env Δ (Tm.rename ρ scrut)
            (.ind I (List.map (Tm.rename ρ) args)) := by
          simpa [Tm.rename] using ihscrut ρ Δ hwk
        have hidx : List.map (substParams (List.map (Tm.rename ρ)
              (List.take sig.params.length args))) sig.indices
            = List.map (Tm.rename ρ)
                (List.map (substParams (List.take sig.params.length args)) sig.indices) := by
          rw [List.map_take]
          exact sigIndices_rename sig hwf args (by omega) ρ
        have hmotive' : HasType env
            (caseMotiveCtx Δ I sig (List.take sig.params.length (List.map (Tm.rename ρ) args)))
            (Tm.rename (Tm.upRenN (n + 1) ρ) C) (.sort i) := by
          have hw := caseMotiveCtx_wk_gen (ρ := ρ) hwk I sig
            (List.take sig.params.length args) hidx
          have hw' : Wk (Tm.upRenN (n + 1) ρ)
              (caseMotiveCtx Γ I sig (List.take sig.params.length args))
              (caseMotiveCtx Δ I sig
                (List.take sig.params.length (List.map (Tm.rename ρ) args))) := by
            rw [hn, ← List.map_take]
            exact hw
          simpa [Tm.rename] using ihmotive (Tm.upRenN (n + 1) ρ) _ hw'
        have hbrs' : List.length (List.map (Tm.rename ρ) brs) = sig.ctors.length := by
          simp only [List.length_map]; omega
        have hxslen : ([scrut] ++ List.reverse (List.drop sig.params.length args)).length
            = n + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil,
            List.length_reverse, List.length_drop]
          omega
        have hxsmap :
            List.map (Tm.rename ρ)
                ([scrut] ++ List.reverse (List.drop sig.params.length args))
              = [Tm.rename ρ scrut] ++
                  List.reverse (List.drop sig.params.length (List.map (Tm.rename ρ) args)) := by
          simp only [List.map_append, List.map_cons, List.map_nil, List.map_reverse,
            List.map_drop]
        rw [rename_substMany, hxslen, hxsmap]
        refine HasType.case Δ I n sig (Tm.rename ρ scrut)
          (Tm.rename (Tm.upRenN (n + 1) ρ) C) (List.map (Tm.rename ρ) brs) i
          (List.map (Tm.rename ρ) args) hsig hn hlen' hscrut' hmotive' hbrs' ?_
        intro c ctor br hctor hbr hpTys hrecTys
        obtain ⟨br0, hbr0, hbrEq⟩ := branch_map hbr
        have h1 := ihbranch c ctor br0 hctor hbr0 hpTys hrecTys ρ Δ hwk
        rw [rename_substMany] at h1
        have hyslen : ([Tm.roll I c (List.take sig.params.length args)] ++
            List.reverse (List.map (substParams (List.take sig.params.length args))
              ctor.indices)).length = n + 1 := by
          rw [List.length_append, List.length_reverse]
          have harity := hsigArity c ctor hctor
          simp only [List.length_cons, List.length_nil, List.length_map]
          omega
        rw [hyslen] at h1
        have hysmap :
            List.map (Tm.rename ρ)
                ([Tm.roll I c (List.take sig.params.length args)] ++
                  List.reverse (List.map (substParams (List.take sig.params.length args))
                    ctor.indices))
              = [Tm.roll I c (List.take sig.params.length (List.map (Tm.rename ρ) args))] ++
                  List.reverse (List.map
                    (substParams (List.take sig.params.length (List.map (Tm.rename ρ) args)))
                    ctor.indices) := by
          simp only [List.map_append, List.map_cons, List.map_nil, List.map_reverse]
          congr 1
          · simp only [Tm.rename, List.map_take]
          · congr 1
            exact (ctorIndices_rename hwf hctor args (by omega) ρ).symm
        rw [hysmap] at h1
        rw [← hbrEq]
        exact h1
  exact key h ρ Δ hwk

/-! ### The invariant is inhabited -/

theorem eq_sig_indexArity : SigIndexArity Eq_sig := by
  intro c ctor hc
  unfold lookupCtor lookup at hc
  cases c with
  | zero =>
      simp [Eq_sig] at hc
      subst hc
      simp [Eq_sig]
  | succ c => simp [Eq_sig] at hc

theorem envIndexArity_Eq : EnvIndexArity [Eq_sig] := by
  intro I sig h
  cases I with
  | zero =>
      simp [lookupInd, lookup] at h
      subst h
      exact eq_sig_indexArity
  | succ I =>
      simp [lookupInd, lookup] at h

end Transport.Mltt
