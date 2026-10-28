import OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyRightInverse
import OAI.AlgebraicGeometry.Comparison.Betti.VectorAntiholomorphicDerivative
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Cauchy Holomorphic Locus -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CauchyHolomorphicLocus.Dolbeault

noncomputable section

section

/-! The actual Cauchy primitive is holomorphic wherever its smooth
input vanishes. This permits polynomial corrections away from the
support when constructing global primitives. -/

open scoped ContDiff

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]

theorem differentiableAt_complex_of_vectorDbar_zero {g : ℂ → F} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) (hd : VectorDbar.Dolbeault.vectorDbar g z = 0) : DifferentiableAt ℂ g z := by
  let D := fderiv ℝ g z
  have ha : OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM ℂ F D = 0 := by
    ext w
    change OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM ℂ F D w = 0
    have h := OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply_smul ℂ F D w 1
    change OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM ℂ F D 1 = 0 at hd
    simpa only [smul_eq_mul, mul_one, hd, smul_zero] using h
  have he : OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM ℂ F D = D := by
    simpa only [ha, add_zero] using OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexDerivativeParts_add ℂ F D
  let L : ℂ →L[ℂ] F :=
    { toFun := OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM ℂ F D
      map_add' := (OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM ℂ F D).map_add
      map_smul' := OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM_apply_smul ℂ F D
      cont := (OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM ℂ F D).cont }
  have hL : L.restrictScalars ℝ = D := by
    ext w
    exact congrArg (fun A : ℂ →L[ℝ] F => A w) he
  exact (hasFDerivAt_of_restrictScalars ℝ hg.hasFDerivAt hL).differentiableAt

theorem vectorCauchyTransform_holomorphic_on_zero [CompleteSpace F] {g : ℂ → F}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) {U : Set ℂ}
    (hzero : ∀ z ∈ U, g z = 0) : DifferentiableOn ℂ (VectorCauchyTransform.Dolbeault.vectorCauchyTransform g) U := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_complex_of_vectorDbar_zero
    ((VectorCauchyTransform.Dolbeault.vectorCauchyTransform_smooth hc hg).differentiable (by simp) z)
  exact (VectorCauchyRightInverse.Dolbeault.vectorDbar_cauchyTransform hg hc z).trans (hzero z hz)

end

/-! The actual antiholomorphic derivative respects finite sums,
differences and germs, and vanishes on holomorphic functions. -/

open scoped _root_.Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]

theorem vectorDbar_add {g h : ℂ → F} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) (hh : DifferentiableAt ℝ h z) :
    VectorDbar.Dolbeault.vectorDbar (fun w => g w + h w) z = VectorDbar.Dolbeault.vectorDbar g z + VectorDbar.Dolbeault.vectorDbar h z := by
  simp only [VectorDbar.Dolbeault.vectorDbar, fderiv_fun_add hg hh, map_add, add_apply]

theorem vectorDbar_sub {g h : ℂ → F} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) (hh : DifferentiableAt ℝ h z) :
    VectorDbar.Dolbeault.vectorDbar (fun w => g w - h w) z = VectorDbar.Dolbeault.vectorDbar g z - VectorDbar.Dolbeault.vectorDbar h z := by
  simp only [VectorDbar.Dolbeault.vectorDbar, fderiv_fun_sub hg hh, map_sub, sub_apply]

theorem vectorDbar_sum {ι : Type*} (s : Finset ι) {g : ι → ℂ → F} {z : ℂ}
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) z) :
    VectorDbar.Dolbeault.vectorDbar (fun w => ∑ i ∈ s, g i w) z = ∑ i ∈ s, VectorDbar.Dolbeault.vectorDbar (g i) z := by
  simp only [VectorDbar.Dolbeault.vectorDbar, fderiv_fun_sum hg, map_sum, sum_apply]

theorem vectorDbar_congr {g h : ℂ → F} {z : ℂ} (he : g =ᶠ[𝓝 z] h) :
    VectorDbar.Dolbeault.vectorDbar g z = VectorDbar.Dolbeault.vectorDbar h z := by
  unfold VectorDbar.Dolbeault.vectorDbar
  rw [he.fderiv_eq]

theorem vectorDbar_zero_of_holomorphic {g : ℂ → F} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) : VectorDbar.Dolbeault.vectorDbar g z = 0 := by
  rw [VectorDbar.Dolbeault.vectorDbar, hg.fderiv_restrictScalars ℝ, OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply]
  change (1 / 2 : ℂ) •
    (fderiv ℂ g z 1 + Complex.I • fderiv ℂ g z (Complex.I • (1 : ℂ))) = 0
  rw [map_smul, smul_smul, Complex.I_mul_I, neg_one_smul, add_neg_cancel, smul_zero]

end

end OAI.AlgebraicGeometry.Comparison.Betti.CauchyHolomorphicLocus.Dolbeault
