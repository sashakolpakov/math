import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodCurvatureInvariance
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicChernComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleChernInvariant
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicProductMaps

/-! # Intrinsic Curvature Invariant -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/- Generic ThetaConstruction specialization of translation invariance of the original curvature.
Pending Lean validation. -/

/-! The transported reference curvature is translation-invariant in
the native abelian group, so it gives the original Chern identity covector. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.nativeCurvatureInvariant_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.nativeCurvatureInvariant_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance PeriodModel.Geometric.AlgebraicPeriodModel.nativeCurvatureInvariant_realLie :
    LieGroup 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) ∞ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.IntrinsicAbelianLieGroup.realLieGroup M.abelian
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem PeriodModel.Geometric.AlgebraicPeriodModel.period_symm_mul (p q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    M.period.symm (p * q) = M.period.symm p + M.period.symm q := by
  apply M.period.injective
  exact (M.period.apply_symm_apply (p * q)).trans ((M.period_add _ _).trans
    (congrArg₂ (fun x y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver => x * y)
      (M.period.apply_symm_apply p) (M.period.apply_symm_apply q))).symm

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeReferenceCurvature_invariant :
    M.nativeReferenceCurvature ∈ AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
      (G := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 2 := by
  rw [AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.mem_invariantForms_iff]
  intro p
  apply Subtype.ext
  have hinv := (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex M.period.symm.contMDiff).mdifferentiable (by simp)
  have hmul := (contMDiff_mul_left (I := 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)) (n := ∞) (a := p)).mdifferentiable (by simp)
  have hadd := (AbelianModuli.ReferenceFamily.PeriodCurvatureInvariance.periodTranslation_contMDiff (ProjectivePeriodData.Geometric.projectivePeriodData F) (M.period.symm p)).mdifferentiable (by simp)
  let C : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (ProjectivePeriodData.Geometric.projectivePeriodData F).space (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus 2 := (PolarizationCurvature.Geometric.referenceTorusCurvature F).val
  have hleft := C.pullback_comp (fun q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver => p * q) hmul M.period.symm hinv
  have hright := C.pullback_comp M.period.symm hinv (fun t => M.period.symm p + t) hadd
  have he : M.period.symm ∘ (fun q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver => p * q) =
      (fun t => M.period.symm p + t) ∘ M.period.symm := funext (M.period_symm_mul p)
  have hc : C.pullback (fun t => M.period.symm p + t) = C :=
    congrArg Subtype.val (AbelianModuli.ReferenceFamily.PeriodCurvatureInvariance.periodCurvature_translation (ProjectivePeriodData.Geometric.projectivePeriodData F) F.riemannForm (M.period.symm p))
  exact hleft.symm.trans ((congrArg (fun k : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver → (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus =>
    C.pullback k) he).trans (hright.trans (congrArg
      (fun b : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (ProjectivePeriodData.Geometric.projectivePeriodData F).space (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus 2 => b.pullback M.period.symm) hc)))

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaClosedForm_invariant :
    M.nativeThetaClosedForm.val ∈ AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
      (G := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 2 :=
  (AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (G := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 2).smul_mem
    (-ConnectionThetaCech.Geometric.chernLogScale) M.nativeReferenceCurvature_invariant

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaChernCovector_eq
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (hdeg : V.degree = U.degree + 1) :
    AbelianModuli.ReferenceFamily.AmpleChernInvariant.nativeChernCovector M.abelian (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left) = M.nativeThetaClosedForm.val 1 :=
  AbelianModuli.ReferenceFamily.AmpleChernInvariant.nativeChernCovector_eq M.abelian (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left) M.nativeThetaClosedForm
    M.nativeThetaClosedForm_invariant (M.nativeThetaChern_comparison U V f g hf hg hdeg)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
