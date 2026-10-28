import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicCurvatureInvariant
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicPeriodDifferential
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod

/-! # Intrinsic Chern Pairing -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicChernPairing.Geometric.AlgebraicPeriodModel

noncomputable section

/-! The original integral form is the actual Chern pairing of the
constructed ample algebraic theta bundle. Pending Lean validation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F)

local instance : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaClosedForm_period (u v : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    M.nativeThetaClosedForm.val 1 ![M.periodDifferential u, M.periodDifferential v] =
      (Complex.I / (2 * (Real.pi : ℂ))) * (PolarizationCurvature.Geometric.referenceCurvature F) 0 ![u, v] := by
  let q := M.period.symm (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  let D : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian →L[ℝ] (ProjectivePeriodData.Geometric.projectivePeriodData F).space :=
    mfderiv 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℝ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space) M.period.symm 1
  have ht (w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
      Analysis.DifferentialForms.Manifold.Charts.chartTangentMap ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart q) q (D (M.periodDifferential w)) = w :=
    (AbelianModuli.ReferenceFamily.Holomorphic.TangentMaps.preferredTangent_identity (E := (ProjectivePeriodData.Geometric.projectivePeriodData F).space) (M := (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus)
      q (D (M.periodDifferential w))).trans (M.inversePeriodRealDifferential_apply w)
  change -ConnectionThetaCech.Geometric.chernLogScale * RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature F.riemannForm ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart q q)
    (fun k => Analysis.DifferentialForms.Manifold.Charts.chartTangentMap ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart q) q
      (D (![M.periodDifferential u, M.periodDifferential v] k))) = _
  have hv : (fun k => Analysis.DifferentialForms.Manifold.Charts.chartTangentMap ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart q) q
      (D (![M.periodDifferential u, M.periodDifferential v] k))) = ![u, v] := by
    funext k
    fin_cases k
    · exact ht u
    · exact ht v
  rw [hv, ConnectionThetaCech.Geometric.neg_chernLogScale]
  change _ = (Complex.I / (2 * (Real.pi : ℂ))) * RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature F.riemannForm 0 ![u, v]
  exact congrArg (fun b : ℂ => (Complex.I / (2 * (Real.pi : ℂ))) * b)
    ((RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature_apply F.riemannForm ((ProjectivePeriodData.Geometric.projectivePeriodData F).periodChart q q) ![u, v]).trans
      (RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature_apply F.riemannForm 0 ![u, v]).symm)

def _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.nativeIntegralPeriod (l : F.lattice) : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian :=
  ⟨M.periodDifferential l.val,
    Submodule.subset_span ((M.periodDifferential_lattice_iff l.val).mpr l.property)⟩

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaChernCovector_integral
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (hdeg : V.degree = U.degree + 1) (l m : F.lattice) :
    AbelianModuli.ReferenceFamily.AmpleChernInvariant.nativeChernCovector M.abelian (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)
      ![(M.nativeIntegralPeriod l).val, (M.nativeIntegralPeriod m).val] =
      (DefinitionsIntegral.Geometric.integralLatticeForm F l m : ℂ) := by
  have hc := congrArg (fun a : Analysis.DifferentialForms.Manifold.Basic.FormValue (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 2 =>
    a ![(M.nativeIntegralPeriod l).val, (M.nativeIntegralPeriod m).val])
      (M.nativeThetaChernCovector_eq U V f g hf hg hdeg)
  exact hc.trans ((M.nativeThetaClosedForm_period l.val m.val).trans
    ((PolarizationCurvature.Geometric.referenceCurvature_integral F) hP l m 0))

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaChernForm_integral
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (hdeg : V.degree = U.degree + 1) (l m : F.lattice) :
    AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)
      (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) = (DefinitionsIntegral.Geometric.integralLatticeForm F l m : ℚ) := by
  have h := (AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod.nativeChernForm_covector M.abelian (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)
    (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m)).symm.trans
      (M.nativeThetaChernCovector_integral U V f g hf hg hdeg l m)
  exact_mod_cast h

include hP in
theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.exists_ample_native_chern_pairing :
    ∃ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left, L.IsAmple ∧
      ∀ l m : F.lattice, AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian L
        (M.nativeIntegralPeriod l) (M.nativeIntegralPeriod m) = (DefinitionsIntegral.Geometric.integralLatticeForm F l m : ℚ) := by
  obtain ⟨U, V, f, g, _, hdeg, _, _, _, _, _, _, hf, hg, _, hamp⟩ :=
    M.exists_ample_theta_quotient (hP := hP)
  exact ⟨RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left, hamp,
    M.nativeThetaChernForm_integral U V f g hf hg hdeg⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicChernPairing.Geometric.AlgebraicPeriodModel
