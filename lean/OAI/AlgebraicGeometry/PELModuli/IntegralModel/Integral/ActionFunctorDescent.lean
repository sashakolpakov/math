import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionCanonicalRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.ActionMatchingCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ReducedFibers

/-! # Action Functor Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionFunctorDescent

noncomputable section

/-! Effective descent of the actual integral-action functor over open
covers of reduced noetherian tests. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionCanonicalRestriction.ActionBaseChange
variable {S B : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (b : B ⟶ S)
    [IsReduced B] [IsLocallyNoetherian B] (C : B.OpenCover) {R : Type} [CommRing R]

theorem existsUnique_action_of_functor_matching
    (ρ : ∀ i, AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback ((C.f i) ≫ b)))
    (hmatch : ∀ i j (T : Over B) [IsReduced T.left]
      (f : T ⟶ Over.mk (C.f i)) (h : T ⟶ Over.mk (C.f j)),
      ActionScheme.restrictIntegralAction A (ρ i) ((Over.map b).map f) =
        ActionScheme.restrictIntegralAction A (ρ j) ((Over.map b).map h)) :
    ∃! q : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback b),
      ∀ i, ActionScheme.restrictIntegralAction A q (ActionCanonicalRestriction.ActionBaseChange.testInclusion b (Over.mk (C.f i))) = ρ i := by
  have : IsReduced (A.pullback b).scheme.left := AbelianModuli.HilbertConstruction.Smooth.ReducedFibers.smooth_reducedSource (A.pullback b).scheme.hom
  let σ := fun i => (IntegralActionBaseChange.ActionBaseChange.actionEquiv (R := R) A b (Over.mk (C.f i))).symm (ρ i)
  have hσ (i) : IntegralActionBaseChange.ActionBaseChange.actionEquiv A b (Over.mk (C.f i)) (σ i) = ρ i :=
    (IntegralActionBaseChange.ActionBaseChange.actionEquiv A b (Over.mk (C.f i))).apply_symm_apply _
  have hm (i j) (T : Over B) [IsReduced T.left]
      (f : T ⟶ Over.mk (C.f i)) (h : T ⟶ Over.mk (C.f j)) :
      ActionScheme.restrictIntegralAction (A.pullback b) (σ i) f =
        ActionScheme.restrictIntegralAction (A.pullback b) (σ j) h := by
    apply (IntegralActionBaseChange.ActionBaseChange.actionEquiv (R := R) A b T).injective
    rw [IntegralActionBaseChange.ActionBaseChange.actionEquiv_natural, IntegralActionBaseChange.ActionBaseChange.actionEquiv_natural, hσ i, hσ j]
    exact hmatch i j T f h
  obtain ⟨q, hq, huniq⟩ := Open.ActionMatchingCompatibility.existsUnique_action_of_reduced_matching C (A.pullback b) σ hm
  refine ⟨q, fun i => ?_, fun r hr => huniq r (fun i => ?_)⟩
  · exact (ActionCanonicalRestriction.ActionBaseChange.actionEquiv_pullback A b (Over.mk (C.f i)) q).trans
      ((congrArg (IntegralActionBaseChange.ActionBaseChange.actionEquiv A b (Over.mk (C.f i))) (hq i)).trans (hσ i))
  · apply (IntegralActionBaseChange.ActionBaseChange.actionEquiv (R := R) A b (Over.mk (C.f i))).injective
    exact (ActionCanonicalRestriction.ActionBaseChange.actionEquiv_pullback A b (Over.mk (C.f i)) r).symm.trans ((hr i).trans (hσ i).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionFunctorDescent
