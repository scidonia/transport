import Transport.Mltt.Core

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

set_option maxHeartbeats 2000000

namespace Transport.Mltt

/-! ## Computation facts for the `Eq` case

The case rule fixes the family, its single constructor, the scrutinee arguments
and the case motive.  The lemmas below record the normal forms the rule's
premises need.  Plain `def`s are semireducible, so each computation is done by
`simp` with the definitions unfolded explicitly. -/

private abbrev jM : Tm := .app (.app (.var 5) (.var 1)) (.var 0)

private abbrev caseArgs : List Tm := [.var 5, .var 4, .var 1]

private abbrev mctx : Ctx := caseMotiveCtx ctxJ 0 Eq_sig (caseArgs.take Eq_sig.params.length)

private abbrev ctor0 : CtorSig := { paramTys := [], recArgs := [], indices := [Tm.var 0] }

private theorem lookupIndStrict_Eq_sig : lookupIndStrict [Eq_sig] 0 = some Eq_sig := by
  simp [lookupIndStrict, lookupInd, lookup, Eq_sig, strictlyPositive, occursInd,
    occursIndFuel, Tm.size, List.any, List.all]

private theorem caseArgs_length :
    caseArgs.length = Eq_sig.params.length + Eq_sig.indices.length := by
  simp [caseArgs, Eq_sig]

private theorem ctor_length : [Tm.var 2].length = Eq_sig.ctors.length := by
  simp [Eq_sig]

private theorem lookupCtor_Eq_sig_zero : lookupCtor Eq_sig 0 = some ctor0 := by
  simp [lookupCtor, lookup, Eq_sig, ctor0]

private theorem lookupCtor_Eq_sig_succ (k : Nat) :
    lookupCtor Eq_sig (Nat.succ k) = none := by
  simp [lookupCtor, lookup, Eq_sig]

private theorem branch_refl :
    Tm.branch [Tm.var 2] 0 = some (Tm.var 2) := by
  simp [Tm.branch]

private theorem ctxLookup_ctxJ_zero :
    ctxLookup ctxJ 0 = some (Tm.ind 0 [Tm.var 5, Tm.var 4, Tm.var 1]) := by
  simp [ctxLookup, ctxJ, eqTy, refl, Tm.shift, Tm.rename, Tm.upRen, Tm.shiftSub]

private theorem ctxLookup_ctxJ_two :
    ctxLookup ctxJ 2
      = some (Tm.app (Tm.app (Tm.var 3) (Tm.var 4))
          (Tm.roll 0 0 [Tm.var 5, Tm.var 4])) := by
  simp [ctxLookup, ctxJ, eqTy, refl, Tm.shift, Tm.rename, Tm.upRen, Tm.shiftSub]

private theorem mctx_lookup_zero :
    ctxLookup mctx 0 = some (Tm.ind 0 [Tm.var 7, Tm.var 6, Tm.var 1]) := by
  simp [mctx, caseMotiveCtx, ctxExtend, ctxExtendMany, ctxLookup, caseArgs, ctxJ,
    eqTy, refl, Tm.shift, Tm.rename, Tm.upRen, Tm.shiftSub, Tm.subst, Tm.upSub,
    substMany, substParams, Eq_sig]

private theorem mctx_lookup_one :
    ctxLookup mctx 1 = some (Tm.var 7) := by
  simp [mctx, caseMotiveCtx, ctxExtend, ctxExtendMany, ctxLookup, caseArgs, ctxJ,
    eqTy, refl, Tm.shift, Tm.rename, Tm.upRen, Tm.shiftSub, Tm.subst, Tm.upSub,
    substMany, substParams, Eq_sig]

private theorem mctx_lookup_five :
    ctxLookup mctx 5
      = some (Tm.pi (Tm.var 7)
          (Tm.pi (Tm.ind 0 [Tm.var 8, Tm.var 7, Tm.var 0]) (Tm.sort 0))) := by
  simp [mctx, caseMotiveCtx, ctxExtend, ctxExtendMany, ctxLookup, caseArgs, ctxJ,
    eqTy, refl, Tm.shift, Tm.rename, Tm.upRen, Tm.shiftSub, Tm.subst, Tm.upSub,
    substMany, substParams, Eq_sig]

private theorem subst0_var1_pi :
    Tm.subst0 (Tm.var 1)
        (Tm.pi (Tm.ind 0 [Tm.var 8, Tm.var 7, Tm.var 0]) (Tm.sort 0))
      = Tm.pi (Tm.ind 0 [Tm.var 7, Tm.var 6, Tm.var 1]) (Tm.sort 0) := by
  simp [Tm.subst0, Tm.subst, Tm.upSub, Tm.shift, Tm.rename, Tm.upRen, Tm.shiftSub]

private theorem subst0_var0_sort :
    Tm.subst0 (Tm.var 0) (Tm.sort 0) = Tm.sort 0 := by
  simp [Tm.subst0, Tm.subst, Tm.upSub, Tm.shift, Tm.rename, Tm.upRen, Tm.shiftSub]

private theorem result_subst :
    substMany ([Tm.var 0] ++ (List.drop Eq_sig.params.length caseArgs).reverse) jM
      = Tm.app (Tm.app (Tm.var 3) (Tm.var 1)) (Tm.var 0) := by
  simp [substMany, Tm.subst, Tm.upSub, Tm.shift, Tm.rename, Tm.upRen, Tm.shiftSub,
    caseArgs, Eq_sig, jM]

private theorem mctx_motive : HasType [Eq_sig] mctx jM (.sort 0) := by
  have h5 : HasType [Eq_sig] mctx (Tm.var 5)
      (Tm.pi (Tm.var 7)
        (Tm.pi (Tm.ind 0 [Tm.var 8, Tm.var 7, Tm.var 0]) (Tm.sort 0))) :=
    HasType.var _ _ _ mctx_lookup_five
  have h1 : HasType [Eq_sig] mctx (Tm.var 1) (Tm.var 7) :=
    HasType.var _ _ _ mctx_lookup_one
  have h0 : HasType [Eq_sig] mctx (Tm.var 0)
      (Tm.ind 0 [Tm.var 7, Tm.var 6, Tm.var 1]) :=
    HasType.var _ _ _ mctx_lookup_zero
  have inner0 := HasType.app (Γ := mctx) (t := Tm.var 5) (u := Tm.var 1)
    (A := Tm.var 7)
    (B := Tm.pi (Tm.ind 0 [Tm.var 8, Tm.var 7, Tm.var 0]) (Tm.sort 0)) h5 h1
  have inner : HasType [Eq_sig] mctx (Tm.app (Tm.var 5) (Tm.var 1))
      (Tm.pi (Tm.ind 0 [Tm.var 7, Tm.var 6, Tm.var 1]) (Tm.sort 0)) := by
    simpa [subst0_var1_pi] using inner0
  have outer0 := HasType.app (Γ := mctx)
    (t := Tm.app (Tm.var 5) (Tm.var 1)) (u := Tm.var 0)
    (A := Tm.ind 0 [Tm.var 7, Tm.var 6, Tm.var 1]) (B := Tm.sort 0) inner h0
  simpa [subst0_var0_sort] using outer0

theorem J_has_type_proof : J_has_type := by
  unfold J_has_type jTerm jResult jMotive
  have hcase : HasType [Eq_sig] ctxJ (.case 0 1 (.var 0) jM [.var 2])
      (substMany ([.var 0] ++ (List.drop Eq_sig.params.length caseArgs).reverse) jM) := by
    refine HasType.case (Γ := ctxJ) (I := 0) (n := 1) (sig := Eq_sig)
      (scrut := Tm.var 0) (C := jM) (brs := [Tm.var 2]) (i := 0) (args := caseArgs)
      lookupIndStrict_Eq_sig rfl caseArgs_length ?_ mctx_motive ctor_length ?_
    · exact HasType.var _ _ _ ctxLookup_ctxJ_zero
    · intro c ctor br hc hb hp hr
      cases c with
      | zero =>
          rw [lookupCtor_Eq_sig_zero] at hc
          injection hc with hctor
          subst hctor
          rw [branch_refl] at hb
          injection hb with hbr
          subst hbr
          exact HasType.var _ _ _ (by
            simp [ctxLookup, ctxJ, eqTy, refl, Tm.shift, Tm.rename, Tm.upRen, Tm.shiftSub,
              substMany, substParams, Tm.subst, Tm.upSub, caseArgs, ctor0, Eq_sig, jM])
      | succ k =>
          rw [lookupCtor_Eq_sig_succ k] at hc
          cases hc
  exact result_subst ▸ hcase

end Transport.Mltt
