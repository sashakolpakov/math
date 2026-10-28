import OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingPointTransitions
import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FrameTrivial

/-! # Constant Projective Map -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConstantProjectiveMap

noncomputable section

/-! Actual constant projective morphisms and vanishing of their constructed original Chern classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def constantSchemeMap (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (T : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints T) : P.toOver ⟶ T :=
  Over.homMk (P.toOver.hom ≫ p.left) (by
    rw [Category.assoc, p.w]
    exact Category.comp_id _)

theorem constantSchemeMap_points (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (T : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints T) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (constantSchemeMap P T p) x = p := by
  apply Over.OverMorphism.ext
  change x.left ≫ (P.toOver.hom ≫ p.left) = p.left
  rw [← Category.assoc, x.w]
  exact Category.id_comp _

def projectiveConstantPoint (n : ℕ) : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver :=
  Classical.choice (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).analyticSpace_nonempty

theorem constantProjectiveMap_firstChern_zero (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {n : ℕ}
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver) :
    First.firstChernClassQ P (GeneratingLineBundle.generatingAlgebraicLineBundle P
      (constantSchemeMap P (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver p)) = 0 := by
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen n (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p)
  apply (GeneratingFrames.generatingAlgebraicSectionFrameAtlas P
    (constantSchemeMap P (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver p)).firstChernClassQ_zero_of_global_frame i
  intro x
  change (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map
    (constantSchemeMap P (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver p) x).left
      (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i
  rw [constantSchemeMap_points]
  exact hi

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConstantProjectiveMap
