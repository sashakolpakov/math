import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.MixedCommutation
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DerivativeApproximation
import OAI.AlgebraicGeometry.Comparison.Betti.CauchyPolynomialDirections
import OAI.AlgebraicGeometry.Comparison.Betti.SeparatedHolomorphicFamilies

/-! # Mixed Slice Parameter Derivative -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.MixedSliceParameterDerivative.Dolbeault

noncomputable section

/-! The full parameter derivative commutes with every holomorphic-line
derivative, as an equality of actual continuous linear maps. -/

open Set
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F]

theorem circleParameterDerivative_holomorphic {g : P × ℂ → F} {S : Set P} {U : Set ℂ}
    (hS : IsOpen S) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g (S ×ˢ U))
    (hhol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => g (p, z)) U) {p : P} (hp : p ∈ S) :
    DifferentiableOn ℂ (fun z => Smooth.ContourDerivative.Dolbeault.circleParameterDerivative g (p, z)) U := by
  apply SeparatedHolomorphicFamilies.Dolbeault.separatingFamily_holomorphic (fun v : P => CauchyPolynomialDirections.Dolbeault.realOperatorComplexEvaluation (F := F) v)
    (fun x y he => ContinuousLinearMap.ext he) hU
    ((Smooth.ContourDerivative.Dolbeault.circleParameterDerivative_smooth (hS.prod hU) hg).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun z hz => ⟨hp, hz⟩))
  intro v
  exact Holomorphic.ParameterDerivatives.Dolbeault.holomorphicSlice_constantDerivative hS hU hg hhol (v, 0) hp

theorem hasFDerivAt_iteratedHolomorphicSlice_parameter {g : P × ℂ → F} {S : Set P} {U : Set ℂ}
    (hS : IsOpen S) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g (S ×ˢ U))
    (hhol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => g (p, z)) U)
    (l : ℕ) {p : P} (hp : p ∈ S) {z : ℂ} (hz : z ∈ U) :
    HasFDerivAt (fun x => iteratedDeriv l (fun w => g (x, w)) z)
      (iteratedDeriv l (fun w => Smooth.ContourDerivative.Dolbeault.circleParameterDerivative g (p, w)) z) p := by
  let G : P × ℂ → F := fun q => iteratedDeriv l (fun w => g (q.1, w)) q.2
  have hG : ContDiffOn ℝ ∞ G (S ×ˢ U) := Smooth.HolomorphicSliceDerivatives.Dolbeault.holomorphicSlice_iteratedDeriv_smooth hS hU hg hhol l
  have hd : DifferentiableAt ℝ G (p, z) :=
    (hG.contDiffAt ((hS.prod hU).mem_nhds ⟨hp, hz⟩)).differentiableAt (by simp)
  have hactual : HasFDerivAt (fun x => G (x, z)) (Smooth.ContourDerivative.Dolbeault.circleParameterDerivative G (p, z)) p := by
    change HasFDerivAt (G ∘ fun x => (x, z))
      ((fderiv ℝ G (p, z)).comp (ContinuousLinearMap.inl ℝ P ℂ)) p
    exact hd.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p z)
  have he : Smooth.ContourDerivative.Dolbeault.circleParameterDerivative G (p, z) =
      iteratedDeriv l (fun w => Smooth.ContourDerivative.Dolbeault.circleParameterDerivative g (p, w)) z := by
    apply ContinuousLinearMap.ext
    intro v
    have h1 := Holomorphic.MixedCommutation.Dolbeault.holomorphicSlice_iteratedDeriv_parameter_commute (q := (p, z)) hS hU hg hhol l ⟨hp, hz⟩ v
    have h2 := Holomorphic.DerivativeApproximation.Dolbeault.holomorphic_iteratedDeriv_map (CauchyPolynomialDirections.Dolbeault.realOperatorComplexEvaluation (F := F) v) hU
      (circleParameterDerivative_holomorphic (p := p) hS hU hg hhol hp) l hz
    exact h1.trans h2
  rw [he] at hactual
  exact hactual

end

end OAI.AlgebraicGeometry.Comparison.Betti.MixedSliceParameterDerivative.Dolbeault
