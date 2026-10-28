import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ConnectionThetaCech
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectivePhaseDefect

/-! # Logarithmic Defect -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The Cech coboundary of the actual complex logarithmic zero-forms
is precisely the original rational logarithmic defect. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

theorem LogarithmicDefect.Geometric.chernLogScale_integer_period (n : ℤ) :
    ConnectionThetaCech.Geometric.chernLogScale * ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = (n : ℂ) := by
  have h : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  unfold ConnectionThetaCech.Geometric.chernLogScale
  rw [mul_left_comm, inv_mul_cancel₀ h, mul_one]

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaLogDefect_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaLogDefect_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaLogarithmCech_apply
    (a : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a)
    (v : Fin 0 → TangentSpace 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) p.val) :
    M.nativeThetaLogarithmCech U V f g hf hg a p v =
      ConnectionThetaCech.Geometric.chernLogScale * M.thetaChernLogCech U V f g hf hg a p := rfl

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaLogarithmCech_delta :
    Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (M.thetaChernCover U V f g hf hg) 0 1 (M.nativeThetaLogarithmCech U V f g hf hg) =
      ComplexMultiplication.HodgeComparison.ProjectivePhaseDefect.CM.Construction.rationalCechManifoldForm (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg) 2
        (DivisorClass.Chern.LogCech.RationalCech.logDefectCech (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
          (M.thetaChernCover U V f g hf hg) (M.thetaChernLogCech U V f g hf hg)
          (M.thetaChernLogCech_cocycle U V f g hf hg)) := by
  funext a
  have hdelta := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechDelta_apply (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 0) (M.thetaChernCover U V f g hf hg)
    1 (M.nativeThetaLogarithmCech U V f g hf hg) a
  refine hdelta.trans ?_
  rw [Fin.sum_univ_three]
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro p
  ext v
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  let W := M.thetaChernCover U V f g hf hg
  let l := M.thetaChernLogCech U V f g hf hg
  let edge := fun j : Fin 3 => DivisorClass.Chern.LogCech.RationalCech.edgeLog T W l j a p
  let hc := M.thetaChernLogCech_cocycle U V f g hf hg a p
  have hs := DivisorClass.Chern.Logarithms.Construction.logarithmicDefect_spec (edge 2) (edge 0) (edge 1) hc
  have hn := congrArg (fun c => ConnectionThetaCech.Geometric.chernLogScale * c) hs
  rw [LogarithmicDefect.Geometric.chernLogScale_integer_period] at hn
  change (1 : ℤ) • (ConnectionThetaCech.Geometric.chernLogScale * edge 0) + (-1 : ℤ) • (ConnectionThetaCech.Geometric.chernLogScale * edge 1) +
    (1 : ℤ) • (ConnectionThetaCech.Geometric.chernLogScale * edge 2) =
      ComplexMultiplication.HodgeComparison.ProjectivePhaseDefect.CM.Construction.rationalLocallyConstantManifoldForm (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) _
        (DivisorClass.Chern.LogCech.RationalCech.logDefectCech T W l (M.thetaChernLogCech_cocycle U V f g hf hg) a) p v
  rw [ComplexMultiplication.HodgeComparison.ProjectivePhaseDefect.CM.Construction.rationalLocallyConstantManifoldForm_apply]
  change _ = (((DivisorClass.Chern.Logarithms.Construction.logarithmicDefect (edge 2) (edge 0) (edge 1) hc : ℤ) : ℚ) : ℂ)
  push_cast
  simp only [one_smul, neg_one_smul]
  calc
    _ = ConnectionThetaCech.Geometric.chernLogScale * (edge 2 + edge 0 - edge 1) := by ring
    _ = _ := hn

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
