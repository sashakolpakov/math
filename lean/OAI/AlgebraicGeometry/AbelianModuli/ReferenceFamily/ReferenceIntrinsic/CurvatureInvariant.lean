import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodCurvatureInvariance
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.ChernComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleChernInvariant

/-! # Curvature Invariant -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The transported reference curvature is translation-invariant in
the native abelian group, so it gives the original Chern identity covector. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeCurvatureInvariant_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeCurvatureInvariant_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeCurvatureInvariant_realLie :
    LieGroup 𝓘(ℝ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) ∞ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.IntrinsicAbelianLieGroup.realLieGroup M.abelian
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.period_symm_mul (p q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    M.period.symm (p * q) = M.period.symm p + M.period.symm q := by
  apply M.period.injective
  exact (M.period.apply_symm_apply (p * q)).trans ((M.period_add _ _).trans
    (congrArg₂ (fun x y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver => x * y)
      (M.period.apply_symm_apply p) (M.period.apply_symm_apply q))).symm

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceCurvature_invariant :
    M.nativeReferenceCurvature ∈ AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (G := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 2 := by
  rw [AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.mem_invariantForms_iff]
  intro p
  apply Subtype.ext
  have hinv := (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex M.period.symm.contMDiff).mdifferentiable (by simp)
  have hmul := (contMDiff_mul_left (I := 𝓘(ℝ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)) (n := ∞) (a := p)).mdifferentiable (by simp)
  have hadd := (PeriodCurvatureInvariance.periodTranslation_contMDiff F.periodData (M.period.symm p)).mdifferentiable (by simp)
  let C : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F.periodData.space F.periodData.periodTorus 2 := F.referenceTorusCurvature.val
  have hleft := C.pullback_comp (fun q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver => p * q) hmul M.period.symm hinv
  have hright := C.pullback_comp M.period.symm hinv (fun t => M.period.symm p + t) hadd
  have he : M.period.symm ∘ (fun q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver => p * q) =
      (fun t => M.period.symm p + t) ∘ M.period.symm := funext (M.period_symm_mul p)
  have hc : C.pullback (fun t => M.period.symm p + t) = C :=
    congrArg Subtype.val (PeriodCurvatureInvariance.periodCurvature_translation F.periodData F.form (M.period.symm p))
  exact hleft.symm.trans ((congrArg (fun k : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver → F.periodData.periodTorus =>
    C.pullback k) he).trans (hright.trans (congrArg
      (fun b : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F.periodData.space F.periodData.periodTorus 2 => b.pullback M.period.symm) hc)))

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaClosedForm_invariant :
    M.nativeThetaClosedForm.val ∈ AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (G := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 2 :=
  (AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (G := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 2).smul_mem
    (-ReferenceTheta.ConnectionCech.chernLogScale) M.nativeReferenceCurvature_invariant

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaChernCovector_eq
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (hdeg : V.degree = U.degree + 1) :
    AmpleChernInvariant.nativeChernCovector M.abelian (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left) = M.nativeThetaClosedForm.val 1 :=
  AmpleChernInvariant.nativeChernCovector_eq M.abelian (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left) M.nativeThetaClosedForm
    M.nativeThetaClosedForm_invariant (M.nativeThetaChern_comparison U V f g hf hg hdeg)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
