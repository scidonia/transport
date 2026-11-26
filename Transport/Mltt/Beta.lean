import Transport.Mltt.Fragment

namespace Transport.Mltt.Beta

open Transport.Mltt
open Transport.Mltt.Subst
open Transport.Mltt.Fragment

/-- Contract the outermost beta redex, if there is one.  This is the
contraction phase of a supercompiler: the residual program is the contractum,
not a reduct reached by a reflexive-transitive step relation. -/
def beta (t : Tm) : Tm :=
  match t with
  | .app (.lam _ body) arg => Tm.subst0 arg body
  | _ => t

/-- Beta contraction preserves typing on the simple fragment.  The proof is
the substitution lemma at the app rule's result type. -/
theorem beta_preserves_hasType {env : Env} {Γ : Ctx} {t A : Tm}
    (ht : HasType env Γ t A) (hs : Simple t) :
    HasType env Γ (beta t) A := by
  induction ht with
  | var Γ x A hx =>
      simpa [beta] using HasType.var Γ x A hx
  | sort Γ i =>
      simpa [beta] using HasType.sort Γ i
  | pi Γ A B i j hA hB ihA ihB =>
      simpa [beta] using HasType.pi Γ A B i j hA hB
  | lam Γ A t B i hA ht ihA iht =>
      simpa [beta] using HasType.lam Γ A t B i hA ht
  | app Γ f u A B hf hu ihf ihu =>
      cases hs with
      | app hsf hsu =>
          cases f with
          | lam C body =>
              cases hsf with
              | lam hsC hsbody =>
                  cases hf with
                  | lam _ _ _ _ _ hC hbody =>
                      simpa [beta] using hasType_subst0_simple hbody hu hsbody hsu
          | var x =>
              simpa [beta] using HasType.app Γ (Tm.var x) u A B hf hu
          | sort i =>
              cases hf
          | pi C D =>
              cases hf
          | app g v =>
              simpa [beta] using HasType.app Γ (Tm.app g v) u A B hf hu
          | fix C body => cases hsf
          | ind I args => cases hsf
          | roll I c args => cases hsf
          | case I n scrut C brs => cases hsf
  | ind Γ I sig args hsig hlen hargs ihargs =>
      cases hs
  | roll Γ I sig c ctor args hsig hctor hlen hparams hctys hrec ihparams ihctys ihrec =>
      cases hs
  | case Γ I n sig scrut C brs i args hsig hn hlen hscrut hmotive hbrs hbranch ihscrut ihmotive ihbranch =>
      cases hs

end Transport.Mltt.Beta
