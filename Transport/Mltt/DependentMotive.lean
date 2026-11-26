import Transport.Mltt.Dependent

/-!
# A dependent motive for the dependent case

`P : Unit -> Type`, with a constructor `p (A : sort 1) : P (Unit.c A)`.
The case below eliminates a `Unit` value at the motive `P scrut`; the branch
is `p A` in the branch telescope `[A : sort 1]`.

The environment gate is a hypothesis, so the example isolates the motive and
branch construction from the positivity computation.
-/

namespace Transport.Mltt.Dependent.Motive

open Transport.Mltt
open Transport.Mltt.Dependent

/-- `P : Unit -> Type`, with `p (A) : P (Unit.c A)`. -/
def P_sig : IndSig where
  params := []
  indices := [.ind 1 []]
  level := 0
  ctors := [
    { paramTys := [.sort 1], recArgs := [], indices := [.roll 1 0 [.var 0]] }
  ]

def pval (a : Tm) : Tm := .roll 0 0 [a]
def unitVal1 : Tm := .roll 1 0 [.sort 0]
def C_motive : Tm := .ind 0 [.var 0]

theorem pval_hasType {Γ : Ctx} {a : Tm}
    (ha : HasType [P_sig, Unit_sig] Γ a (.sort 1))
    (hlookP : lookupIndStrict [P_sig, Unit_sig] 0 = some P_sig) :
    HasTypeDep [P_sig, Unit_sig] Γ (pval a) (.ind 0 [.roll 1 0 [a]]) := by
  have hctor : lookupCtor P_sig 0 = some (P_sig.ctors[0]) := rfl
  have hlen : [a].length = P_sig.params.length + P_sig.ctors[0].paramTys.length
      + P_sig.ctors[0].recArgs.length := by simp [P_sig]
  simpa [P_sig, pval, substMany, Tm.subst] using
    (HasTypeDep.rollDep Γ 0 P_sig 0 (P_sig.ctors[0]) [a] hlookP hctor hlen
      (by intro i x A hx _; simp [P_sig] at hx)
      (by
        intro i x A hx hA
        cases i with
        | zero =>
            simp [P_sig, substMany, Tm.subst] at hx hA
            subst x
            subst A
            exact HasTypeDep.ofHasType ha
        | succ i =>
            simp [P_sig] at hx)
      (by intro i r idxs _ hidx; simp [P_sig] at hidx))

theorem unit_caseDep_motive
    (hlookU : lookupIndStrict [P_sig, Unit_sig] 1 = some Unit_sig)
    (hlookP : lookupIndStrict [P_sig, Unit_sig] 0 = some P_sig)
    (hscrut : HasTypeDep [P_sig, Unit_sig] [] unitVal1 (.ind 1 []))
    (hmotive : HasTypeDep [P_sig, Unit_sig]
      (caseMotiveCtx [] 1 Unit_sig (List.take Unit_sig.params.length ([] : List Tm)))
      C_motive (.sort 1)) :
    HasTypeDep [P_sig, Unit_sig] []
      (.case 1 0 unitVal1 C_motive [pval (.var 0)])
      (.ind 0 [unitVal1]) := by
  simpa [C_motive, substMany, Tm.subst, unitVal1] using
    (HasTypeDep.caseDep [] 1 0 Unit_sig unitVal1 C_motive
      [pval (.var 0)] 1 []
      hlookU rfl rfl hscrut hmotive rfl
      (by
        intro c ctor br hctor hbr
        cases c with
        | zero =>
            simp [Unit_sig, lookupCtor, lookup] at hctor
            subst hctor
            simp [Tm.branch] at hbr
            subst hbr
            simpa [branchCtx, branchTys, branchTy, branchVars, ctxExtendMany, ctxExtend,
              substMany, Tm.subst, Unit_sig, P_sig, C_motive, pval, unitVal1]
              using (pval_hasType (Γ := [.sort 1])
                  (a := .var 0)
                  (by
                    simpa [Tm.shift, Tm.rename] using
                      (HasType.var [.sort 1] 0 (.sort 1)
                        (by simp [ctxLookup, Tm.shift, Tm.rename])))
                  hlookP)
        | succ c =>
            simp [Unit_sig, lookupCtor, lookup] at hctor))

end Transport.Mltt.Dependent.Motive
