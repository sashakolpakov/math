import OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicDerivativeCommutation
import OAI.AlgebraicGeometry.Comparison.Betti.CauchyHolomorphicLocus

/-! # Parameter Derivatives -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ParameterDerivatives.Dolbeault

noncomputable section

/-! For a smooth family holomorphic in its complex-line variable,
every ordinary constant directional derivative remains holomorphic in
that variable. The proof uses actual mixed Fréchet derivatives. -/

open Filter Set
open scoped _root_.Topology ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]

omit [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
theorem constantDerivative_smooth_on {g : P × ℂ → F} {S : Set P} {U : Set ℂ}
    (hS : IsOpen S) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g (S ×ˢ U)) (v : P × ℂ) :
    ContDiffOn ℝ ∞ (fun q => fderiv ℝ g q v) (S ×ˢ U) :=
  (ContinuousLinearMap.apply ℝ F v).contDiff.comp_contDiffOn
    (hg.fderiv_of_isOpen (hS.prod hU) (m := ∞) (by simp))

theorem holomorphicSlice_constantDerivative {g : P × ℂ → F} {S : Set P} {U : Set ℂ}
    (hS : IsOpen S) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g (S ×ˢ U))
    (hhol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => g (p, z)) U)
    (v : P × ℂ) {p : P} (hp : p ∈ S) :
    DifferentiableOn ℂ (fun z => fderiv ℝ g (p, z) v) U := by
  have hDs := constantDerivative_smooth_on hS hU hg v
  intro z hz
  have hq : (p, z) ∈ S ×ˢ U := ⟨hp, hz⟩
  have hD := (hDs.contDiffAt ((hS.prod hU).mem_nhds hq)).differentiableAt (by simp)
  have hSlice := hD.comp z (hasFDerivAt_prodMk_right (𝕜 := ℝ) p z).differentiableAt
  apply DifferentiableAt.differentiableWithinAt
  apply CauchyHolomorphicLocus.Dolbeault.differentiableAt_complex_of_vectorDbar_zero hSlice
  change VectorDbar.Dolbeault.vectorDbar (fun w => fderiv ℝ g (p, w) v) z = 0
  rw [VectorAntiholomorphicDerivative.Dolbeault.vectorDbar_product_slice hD]
  apply AntiholomorphicDerivativeCommutation.Dolbeault.vectorAntiDerivative_constantDerivative_zero
    (hg.contDiffAt ((hS.prod hU).mem_nhds hq))
  filter_upwards [(hS.prod hU).mem_nhds hq] with q hq'
  have hreal := (hg.contDiffAt ((hS.prod hU).mem_nhds hq')).differentiableAt (by simp)
  exact (VectorAntiholomorphicDerivative.Dolbeault.vectorDbar_product_slice hreal).symm.trans
    (CauchyHolomorphicLocus.Dolbeault.vectorDbar_zero_of_holomorphic ((hhol q.1 hq'.1).differentiableAt (hU.mem_nhds hq'.2)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ParameterDerivatives.Dolbeault
