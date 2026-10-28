import OAI.RepresentationTheory.Theta.Geometric.PolarizationConnection

/-! # Antiholomorphic Potential -/

namespace OAI.RepresentationTheory.Theta.Geometric.AntiholomorphicPotential

noncomputable section

/-! The smooth antiholomorphic potential has exactly the translation
factor of the original polarization line bundle. -/

set_option backward.isDefEq.respectTransparency false
open scoped ContDiff

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

local instance antiholomorphicPotential_realFiniteDimensional : FiniteDimensional ℝ V :=
  FiniteDimensional.trans ℝ ℂ V

def antiholomorphicPolarizationPotential (a z : V) : ℂ := (Real.pi : ℂ) * H z a

theorem antiholomorphicPolarizationPotential_contDiff (a : V) :
    ContDiff ℝ ∞ (antiholomorphicPolarizationPotential H a) :=
  ((Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitianBilin H).flip a).contDiff.const_smul (Real.pi : ℂ)

theorem antiholomorphicPolarizationPotential_hasFDerivAt (a z : V) :
    HasFDerivAt (antiholomorphicPolarizationPotential H a)
      ((Real.pi : ℂ) • (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitianBilin H).flip a) z :=
  ((Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitianBilin H).flip a).hasFDerivAt.const_smul (Real.pi : ℂ)

theorem antiholomorphicPolarizationPotential_fderiv (a z v : V) :
    fderiv ℝ (antiholomorphicPolarizationPotential H a) z v = (Real.pi : ℂ) * H v a := by
  rw [(antiholomorphicPolarizationPotential_hasFDerivAt H a z).fderiv]
  rfl

theorem antiholomorphicPolarizationPotential_dbar (a z v : V) :
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM V ℂ
      (fderiv ℝ (antiholomorphicPolarizationPotential H a) z) v = (Real.pi : ℂ) * H v a := by
  rw [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply,
    antiholomorphicPolarizationPotential_fderiv, antiholomorphicPolarizationPotential_fderiv]
  have h := congrArg (fun f : V →ₗ[ℂ] ℂ => f a) (H.map_smulₛₗ Complex.I v)
  change H (Complex.I • v) a = star Complex.I * H v a at h
  rw [h]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V] in
theorem antiholomorphicPolarizationPotential_translation (a z l : V) :
    antiholomorphicPolarizationPotential H a (z + l) - antiholomorphicPolarizationPotential H a z =
      (Real.pi : ℂ) * H l a := by
  simp only [antiholomorphicPolarizationPotential, map_add, LinearMap.add_apply, mul_add]
  exact add_sub_cancel_left _ _

variable {L I : Type} [AddCommGroup L] [Module ℤ L] [LinearOrder I]
    (b : Module.Basis I ℤ L) (B : LinearMap.BilinForm ℤ L) (e : L →+ V)

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V] in
theorem antiholomorphicPotential_exponential_translation (a z : V) (l : L) :
    Complex.exp (antiholomorphicPolarizationPotential H a (z + e l) -
      antiholomorphicPolarizationPotential H a z) =
        PolarizationAutomorphy.polarizationAutomorphy b B e H l (z + a) / PolarizationAutomorphy.polarizationAutomorphy b B e H l z := by
  rw [antiholomorphicPolarizationPotential_translation]
  simp only [PolarizationAutomorphy.polarizationAutomorphy, map_add, ← Complex.exp_sub]
  congr 1
  ring

end

end OAI.RepresentationTheory.Theta.Geometric.AntiholomorphicPotential
