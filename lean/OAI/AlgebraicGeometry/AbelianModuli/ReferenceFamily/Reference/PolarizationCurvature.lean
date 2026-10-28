import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PolarizationMetric
import OAI.RepresentationTheory.Theta.Geometric.Torus.PolarizationCurvature

/-! # Polarization Curvature -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The curvature of the constructed reference connection is closed,
positive, of type (1,1), and has exactly the original integral pairing.
The form descends in the actual period-torus tangent charts. -/

open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z)

def Fiber.ReferenceAnalyticFiber.referenceCurvature : Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fiber.ReferenceTangent s) 2 := RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature F.form

theorem Fiber.ReferenceAnalyticFiber.referenceCurvature_integral (hP : P.IsAdmissible)
    (l m : P.lattice) (w : Fiber.ReferenceTangent s) :
    (Complex.I / (2 * (Real.pi : ℂ))) * F.referenceCurvature w
      ![F.latticeEmbedding l, F.latticeEmbedding m] = (P.integralForm l m : ℂ) := by
  rw [Fiber.ReferenceAnalyticFiber.referenceCurvature, RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature_normalized _ F.hermitian]
  change ((F.form (F.latticeEmbedding l) (F.latticeEmbedding m)).im : ℂ) = _
  have h : (F.form (F.latticeEmbedding l) (F.latticeEmbedding m)).im =
      (P.integralForm l m : ℝ) := F.latticeEquiv_polarization hP l m
  exact_mod_cast h

theorem Fiber.ReferenceAnalyticFiber.referenceCurvature_positive (w v : Fiber.ReferenceTangent s) (hv : v ≠ 0) :
    0 < ((Complex.I / (2 * (Real.pi : ℂ))) * F.referenceCurvature w ![v, Complex.I • v]).re :=
  RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature_positive F.form F.hermitian F.positive w v hv

def Fiber.ReferenceAnalyticFiber.referenceTorusCurvature : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F.periodData.space F.periodData.periodTorus 2 :=
  F.periodData.torusCurvature F.form

theorem Fiber.ReferenceAnalyticFiber.referenceTorusCurvature_closed : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d F.referenceTorusCurvature = 0 :=
  F.periodData.torusCurvature_closed F.form

theorem Fiber.ReferenceAnalyticFiber.referenceTorusCurvature_type :
    Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree F.periodData.space F.periodData.periodTorus 1 1 F.referenceTorusCurvature.val :=
  F.periodData.torusCurvature_hasTangentBidegree F.form

theorem Fiber.ReferenceAnalyticFiber.referenceTorusCurvature_positive (q : F.periodData.periodTorus)
    (v : TangentSpace 𝓘(ℝ, F.periodData.space) q) (hv : v ≠ 0) :
    0 < ((Complex.I / (2 * (Real.pi : ℂ))) *
      F.referenceTorusCurvature q ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul q Complex.I v]).re :=
  F.periodData.torusCurvature_positive F.form F.hermitian F.positive q v hv

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
