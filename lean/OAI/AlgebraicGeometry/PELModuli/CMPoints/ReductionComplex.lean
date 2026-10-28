import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduction
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeClosed

/-! # Reduction Complex -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ReductionComplex

noncomputable section

/-! Reduction does not change the actual complex point space, even after
an arbitrary change of base to the complex numbers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem reduction_baseChange_complexPoints_surjective
    {S : Scheme.{0}} (X : Over S) (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) :
    Function.Surjective (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
      ((Over.pullback c).map (IntegralModel.Reduction.reductionι X))) := by
  intro p
  let T : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
  let : IsReduced ((Over.map c).obj T).left := inferInstanceAs (IsReduced Foundations.Scheme.ProjectiveSpace.complexBase)
  let e := (Over.mapPullbackAdj c).homEquiv T X
  let er := (Over.mapPullbackAdj c).homEquiv T (IntegralModel.Reduction.reduction X)
  let f := IntegralModel.Reduction.factorToReduction (e.symm p)
  refine ⟨er f, ?_⟩
  change er f ≫ (Over.pullback c).map (IntegralModel.Reduction.reductionι X) = p
  rw [← (Over.mapPullbackAdj c).homEquiv_naturality_right]
  change e (IntegralModel.Reduction.factorToReduction (e.symm p) ≫ IntegralModel.Reduction.reductionι X) = p
  rw [IntegralModel.Reduction.factorToReduction_ι, Equiv.apply_symm_apply]

def reductionComplexPointHomeomorph
    {S : Scheme.{0}} (X : Over S) (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints ((Over.pullback c).obj (IntegralModel.Reduction.reduction X)) ≃ₜ
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints ((Over.pullback c).obj X) := by
  let f := (Over.pullback c).map (IntegralModel.Reduction.reductionι X)
  let : IsClosedImmersion f.left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) _ _ inferInstance
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion f).toHomeomorphOfSurjective
    (reduction_baseChange_complexPoints_surjective X c)

theorem reductionComplexPointHomeomorph_apply
    {S : Scheme.{0}} (X : Over S) (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ S)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints ((Over.pullback c).obj (IntegralModel.Reduction.reduction X))) :
    reductionComplexPointHomeomorph X c p =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map ((Over.pullback c).map (IntegralModel.Reduction.reductionι X)) p := rfl

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ReductionComplex
