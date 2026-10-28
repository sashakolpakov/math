import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionCanonicalRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ActionMatchingCompatibility

/-! # Action Functor Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ActionFunctorDescent

noncomputable section

/-! Effective descent of the actual integral-action functor over open
covers of arbitrary tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionCanonicalRestriction.ActionBaseChange
variable {S B : Scheme.{0}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (b : B ⟶ S)
    (C : B.OpenCover) {R : Type} [CommRing R]

theorem existsUnique_action_of_functor_matching
    (ρ : ∀ i, ActionData.IntegralAction R (A.pullback ((C.f i) ≫ b)))
    (hmatch : ∀ i j (T : Over B)
      (f : T ⟶ Over.mk (C.f i)) (h : T ⟶ Over.mk (C.f j)),
      PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A (ρ i) ((Over.map b).map f) =
        PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A (ρ j) ((Over.map b).map h)) :
    ∃! q : ActionData.IntegralAction R (A.pullback b),
      ∀ i, PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction A q (PELModuli.IntegralModel.ActionCanonicalRestriction.ActionBaseChange.testInclusion b (Over.mk (C.f i))) = ρ i := by
  let σ := fun i => (PELModuli.IntegralModel.Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv (R := R) A b (Over.mk (C.f i))).symm (ρ i)
  have hσ (i) : PELModuli.IntegralModel.Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv A b (Over.mk (C.f i)) (σ i) = ρ i :=
    (PELModuli.IntegralModel.Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv A b (Over.mk (C.f i))).apply_symm_apply _
  have hm (i j) (T : Over B)
      (f : T ⟶ Over.mk (C.f i)) (h : T ⟶ Over.mk (C.f j)) :
      PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction (A.pullback b) (σ i) f =
        PELModuli.IntegralModel.Integral.ActionScheme.restrictIntegralAction (A.pullback b) (σ j) h := by
    apply (PELModuli.IntegralModel.Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv (R := R) A b T).injective
    rw [PELModuli.IntegralModel.Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv_natural, PELModuli.IntegralModel.Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv_natural, hσ i, hσ j]
    exact hmatch i j T f h
  obtain ⟨q, hq, huniq⟩ := Open.ActionMatchingCompatibility.existsUnique_action_of_matching C (A.pullback b) σ hm
  refine ⟨q, fun i => ?_, fun r hr => huniq r (fun i => ?_)⟩
  · exact (PELModuli.IntegralModel.ActionCanonicalRestriction.ActionBaseChange.actionEquiv_pullback A b (Over.mk (C.f i)) q).trans
      ((congrArg (PELModuli.IntegralModel.Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv A b (Over.mk (C.f i))) (hq i)).trans (hσ i))
  · apply (PELModuli.IntegralModel.Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv (R := R) A b (Over.mk (C.f i))).injective
    exact (PELModuli.IntegralModel.ActionCanonicalRestriction.ActionBaseChange.actionEquiv_pullback A b (Over.mk (C.f i)) r).symm.trans ((hr i).trans (hσ i).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ActionFunctorDescent
