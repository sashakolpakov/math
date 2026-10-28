import OAI.RepresentationTheory.Theta.Geometric.PolarizationAutomorphy
import OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-! # Polarization Connection -/

namespace OAI.RepresentationTheory.Theta.Geometric.PolarizationConnection

noncomputable section

/-! The Gaussian metric connection for the original polarization,
including its actual derivative and change of frame. -/

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]
  (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

local instance : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V

def polarizationLogMetric (z : V) : ℂ := (Real.log (PolarizationAutomorphy.polarizationMetricWeight H z) : ℂ)

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V] in
theorem polarizationLogMetric_eq (hsym : ∀ u v, H v u = star (H u v)) (z : V) :
    polarizationLogMetric H z = -(Real.pi : ℂ) * H z z := by
  have him := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitian_imaginary_self H hsym z
  apply Complex.ext
  · simp [polarizationLogMetric, PolarizationAutomorphy.polarizationMetricWeight, Complex.mul_re]
  · simp [polarizationLogMetric, Complex.mul_im, him]

theorem polarizationLogMetric_hasFDerivAt (hsym : ∀ u v, H v u = star (H u v)) (z : V) :
    HasFDerivAt (polarizationLogMetric H)
      (-(Real.pi : ℂ) • (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitianBilin H z +
        (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitianBilin H).flip z)) z := by
  have h := ((Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitianBilin H).hasFDerivAt_of_bilinear
    (hasFDerivAt_id z) (hasFDerivAt_id z)).const_smul (-(Real.pi : ℂ))
  convert! h using 1
  funext y
  exact polarizationLogMetric_eq H hsym y

theorem polarizationLogMetric_fderiv (hsym : ∀ u v, H v u = star (H u v)) (z v : V) :
    fderiv ℝ (polarizationLogMetric H) z v = -(Real.pi : ℂ) * (H z v + H v z) := by
  rw [(polarizationLogMetric_hasFDerivAt H hsym z).fderiv]
  rfl

def polarizationConnection : V →L[ℝ] V →L[ℝ] ℂ :=
  -(Real.pi : ℂ) • Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitianBilin H

theorem polarizationConnection_eq_metric_derivative (hsym : ∀ u v, H v u = star (H u v)) (z : V) :
    polarizationConnection H z =
      OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM V ℂ (fderiv ℝ (polarizationLogMetric H) z) := by
  ext v
  rw [OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM_apply, polarizationLogMetric_fderiv H hsym,
    polarizationLogMetric_fderiv H hsym]
  change -(Real.pi : ℂ) * H z v =
    (1 / 2 : ℂ) * (-(Real.pi : ℂ) * (H z v + H v z) -
      Complex.I * (-(Real.pi : ℂ) * (H z (Complex.I • v) + H (Complex.I • v) z)))
  rw [map_smul, hsym z (Complex.I • v), map_smul, hsym z v]
  simp only [smul_eq_mul, star_mul, Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

variable {L I : Type} [AddCommGroup L] [Module ℤ L] [LinearOrder I]
  (b : Module.Basis I ℤ L) (B : LinearMap.BilinForm ℤ L) (e : L →+ V)

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] in
theorem polarizationAutomorphy_hasFDerivAt (l : L) (z : V) :
    HasFDerivAt (PolarizationAutomorphy.polarizationAutomorphy b B e H l)
      (PolarizationAutomorphy.polarizationAutomorphy b B e H l z • ((Real.pi : ℂ) • (H (e l)).toContinuousLinearMap)) z := by
  have h := (((H (e l)).toContinuousLinearMap.hasFDerivAt (x := z)).const_add
    (Complex.I * (LatticeSemicharacter.latticeQuadraticRefinement b B l : ℂ))).add_const (H (e l) (e l) / 2)
  exact (h.const_smul (Real.pi : ℂ)).cexp

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] in
theorem polarizationAutomorphy_fderiv (l : L) (z v : V) :
    fderiv ℂ (PolarizationAutomorphy.polarizationAutomorphy b B e H l) z v =
      PolarizationAutomorphy.polarizationAutomorphy b B e H l z * ((Real.pi : ℂ) * H (e l) v) := by
  rw [(polarizationAutomorphy_hasFDerivAt H b B e l z).fderiv]
  rfl

theorem polarizationConnection_translation (l : L) (z v : V) :
    polarizationConnection H (z + e l) v = polarizationConnection H z v -
      (PolarizationAutomorphy.polarizationAutomorphy b B e H l z)⁻¹ * fderiv ℂ (PolarizationAutomorphy.polarizationAutomorphy b B e H l) z v := by
  rw [polarizationAutomorphy_fderiv, ← mul_assoc,
    inv_mul_cancel₀ (PolarizationAutomorphy.polarizationAutomorphy_ne_zero b B e H l z), one_mul]
  change -(Real.pi : ℂ) * H (z + e l) v = -(Real.pi : ℂ) * H z v - (Real.pi : ℂ) * H (e l) v
  rw [map_add, LinearMap.add_apply]
  ring

end

end OAI.RepresentationTheory.Theta.Geometric.PolarizationConnection
