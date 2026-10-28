import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationMetric
import OAI.RepresentationTheory.Theta.Geometric.Torus.PolarizationCurvature

/-! # Polarization Curvature -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationCurvature.Geometric

noncomputable section

/-! The curvature of the constructed reference connection is closed,
positive, of type (1,1), and has exactly the original integral pairing.
The form descends in the actual period-torus tangent charts. -/

open scoped _root_.Manifold ContDiff

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} (F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix)

def referenceCurvature : Analysis.DifferentialForms.Manifold.Basic.SmoothForm (DefinitionsIntegral.Tangent dim) 2 := RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature F.riemannForm

theorem referenceCurvature_integral (hP : matrix.transpose = -matrix)
    (l m : F.lattice) (w : DefinitionsIntegral.Tangent dim) :
    (Complex.I / (2 * (Real.pi : ℂ))) * (referenceCurvature F) w
      ![(PolarizationFactor.Geometric.latticeEmbedding F) l, (PolarizationFactor.Geometric.latticeEmbedding F) m] = ((DefinitionsIntegral.Geometric.integralLatticeForm F) l m : ℂ) := by
  rw [referenceCurvature, RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature_normalized _ F.hermitian]
  change ((F.riemannForm ((PolarizationFactor.Geometric.latticeEmbedding F) l) ((PolarizationFactor.Geometric.latticeEmbedding F) m)).im : ℂ) = _
  have h : (F.riemannForm ((PolarizationFactor.Geometric.latticeEmbedding F) l) ((PolarizationFactor.Geometric.latticeEmbedding F) m)).im =
      ((DefinitionsIntegral.Geometric.integralLatticeForm F) l m : ℝ) := PolarizationFactor.Geometric.latticeEquiv_polarization F hP l m
  exact_mod_cast h

theorem referenceCurvature_positive (w v : DefinitionsIntegral.Tangent dim) (hv : v ≠ 0) :
    0 < ((Complex.I / (2 * (Real.pi : ℂ))) * (referenceCurvature F) w ![v, Complex.I • v]).re :=
  RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature_positive F.riemannForm F.hermitian F.positive w v hv

def referenceTorusCurvature : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (ProjectivePeriodData.Geometric.projectivePeriodData F).space (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus 2 :=
  (ProjectivePeriodData.Geometric.projectivePeriodData F).torusCurvature F.riemannForm

theorem referenceTorusCurvature_closed : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (referenceTorusCurvature F) = 0 :=
  (ProjectivePeriodData.Geometric.projectivePeriodData F).torusCurvature_closed F.riemannForm

theorem referenceTorusCurvature_type :
    Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree (ProjectivePeriodData.Geometric.projectivePeriodData F).space (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus 1 1 (referenceTorusCurvature F).val :=
  (ProjectivePeriodData.Geometric.projectivePeriodData F).torusCurvature_hasTangentBidegree F.riemannForm

theorem referenceTorusCurvature_positive (q : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus)
    (v : TangentSpace 𝓘(ℝ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space) q) (hv : v ≠ 0) :
    0 < ((Complex.I / (2 * (Real.pi : ℂ))) *
      (referenceTorusCurvature F) q ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul q Complex.I v]).re :=
  (ProjectivePeriodData.Geometric.projectivePeriodData F).torusCurvature_positive F.riemannForm F.hermitian F.positive q v hv

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.PolarizationCurvature.Geometric
