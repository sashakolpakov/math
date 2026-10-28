import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.DirectionalCommutation
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.HolomorphicSliceDerivatives
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ParameterDerivatives

/-! # Mixed Commutation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.MixedCommutation.Dolbeault

noncomputable section

/-! Actual parameter differentiation commutes with differentiation in
the holomorphic line, using the original real second derivative. -/

open Set Filter
open scoped ContDiff _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem holomorphicSlice_deriv_parameter_commute {g : P × ℂ → F} {S : Set P} {U : Set ℂ}
    (hS : IsOpen S) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g (S ×ˢ U))
    (hhol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => g (p, z)) U)
    {q : P × ℂ} (hq : q ∈ S ×ˢ U) (v : P) :
    fderiv ℝ (fun y : P × ℂ => deriv (fun z => g (y.1, z)) y.2) q (v, 0) =
      deriv (fun z => fderiv ℝ g (q.1, z) (v, 0)) q.2 := by
  have hqg := hg.contDiffAt ((hS.prod hU).mem_nhds hq)
  have he : (fun y : P × ℂ => deriv (fun z => g (y.1, z)) y.2) =ᶠ[𝓝 q]
      (fun y => fderiv ℝ g y (0, 1)) := by
    filter_upwards [(hS.prod hU).mem_nhds hq] with y hy
    exact Smooth.HolomorphicSliceDerivatives.Dolbeault.holomorphicSlice_deriv_eq_real
      ((hg.contDiffAt ((hS.prod hU).mem_nhds hy)).differentiableAt (by simp))
      ((hhol y.1 hy.1 y.2 hy.2).differentiableAt (hU.mem_nhds hy.2))
  have hD : DifferentiableAt ℝ (fun y => fderiv ℝ g y (v, 0)) q :=
    ((ParameterDerivatives.Dolbeault.constantDerivative_smooth_on hS hU hg (v, 0)).contDiffAt
      ((hS.prod hU).mem_nhds hq)).differentiableAt (by simp)
  have hDh : DifferentiableAt ℂ (fun z => fderiv ℝ g (q.1, z) (v, 0)) q.2 :=
    ((ParameterDerivatives.Dolbeault.holomorphicSlice_constantDerivative hS hU hg hhol (v, 0) hq.1) q.2 hq.2).differentiableAt
      (hU.mem_nhds hq.2)
  rw [he.fderiv_eq, Smooth.HolomorphicSliceDerivatives.Dolbeault.holomorphicSlice_deriv_eq_real hD hDh]
  exact Smooth.DirectionalCommutation.Dolbeault.smooth_constantDerivative_commute hqg (0, 1) (v, 0)

theorem holomorphicSlice_iteratedDeriv_parameter_commute [CompleteSpace F]
    {g : P × ℂ → F} {S : Set P} {U : Set ℂ}
    (hS : IsOpen S) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g (S ×ˢ U))
    (hhol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => g (p, z)) U)
    (l : ℕ) {q : P × ℂ} (hq : q ∈ S ×ˢ U) (v : P) :
    fderiv ℝ (fun y : P × ℂ => iteratedDeriv l (fun z => g (y.1, z)) y.2) q (v, 0) =
      iteratedDeriv l (fun z => fderiv ℝ g (q.1, z) (v, 0)) q.2 := by
  induction l generalizing q with
  | zero => rfl
  | succ l ih =>
    let G : P × ℂ → F := fun y => iteratedDeriv l (fun z => g (y.1, z)) y.2
    have hG : ContDiffOn ℝ ∞ G (S ×ˢ U) := Smooth.HolomorphicSliceDerivatives.Dolbeault.holomorphicSlice_iteratedDeriv_smooth hS hU hg hhol l
    have hGh : ∀ p ∈ S, DifferentiableOn ℂ (fun z => G (p, z)) U :=
      fun p hp => DerivativeApproximation.Dolbeault.holomorphic_iteratedDeriv_on (hhol p hp) hU l
    simp only [iteratedDeriv_succ]
    change fderiv ℝ (fun y : P × ℂ => deriv (fun z => G (y.1, z)) y.2) q (v, 0) = _
    rw [holomorphicSlice_deriv_parameter_commute hS hU hG hGh hq v]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hU.mem_nhds hq.2] with z hz
    exact ih (q := (q.1, z)) ⟨hq.1, hz⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.MixedCommutation.Dolbeault
