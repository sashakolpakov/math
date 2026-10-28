import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DerivativeApproximation
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Holomorphic Slice Derivatives -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.HolomorphicSliceDerivatives.Dolbeault

noncomputable section

/-! Complex-line derivatives of a smooth holomorphic family are actual
constant real derivatives of the joint function, and remain jointly smooth. -/

open Set _root_.Metric
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem holomorphicSlice_deriv_eq_real {g : P × ℂ → F} {q : P × ℂ}
    (hg : DifferentiableAt ℝ g q) (hhol : DifferentiableAt ℂ (fun z => g (q.1, z)) q.2) :
    deriv (fun z => g (q.1, z)) q.2 = fderiv ℝ g q (0, 1) := by
  have hs : HasFDerivAt (fun z => g (q.1, z))
      ((fderiv ℝ g q).comp (ContinuousLinearMap.inr ℝ P ℂ)) q.2 :=
    hg.hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)
  have he := hs.unique (hhol.hasFDerivAt.restrictScalars ℝ)
  exact (congrArg (fun L : ℂ →L[ℝ] F => L 1) he).symm

theorem holomorphicSlice_deriv_smooth {g : P × ℂ → F} {S : Set P} {U : Set ℂ}
    (hS : IsOpen S) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g (S ×ˢ U))
    (hhol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => g (p, z)) U) :
    ContDiffOn ℝ ∞ (fun q : P × ℂ => deriv (fun z => g (q.1, z)) q.2) (S ×ˢ U) := by
  have hD : ContDiffOn ℝ ∞ (fun q => fderiv ℝ g q (0, 1)) (S ×ˢ U) :=
    (ContinuousLinearMap.apply ℝ F ((0, 1) : P × ℂ)).contDiff.comp_contDiffOn
      (hg.fderiv_of_isOpen (hS.prod hU) (m := ∞) (by simp))
  apply hD.congr
  intro q hq
  exact holomorphicSlice_deriv_eq_real
    ((hg.contDiffAt ((hS.prod hU).mem_nhds hq)).differentiableAt (by simp))
    ((hhol q.1 hq.1 q.2 hq.2).differentiableAt (hU.mem_nhds hq.2))

theorem holomorphicSlice_iteratedDeriv_smooth [CompleteSpace F]
    {g : P × ℂ → F} {S : Set P} {U : Set ℂ}
    (hS : IsOpen S) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g (S ×ˢ U))
    (hhol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => g (p, z)) U) (l : ℕ) :
    ContDiffOn ℝ ∞ (fun q : P × ℂ => iteratedDeriv l (fun z => g (q.1, z)) q.2) (S ×ˢ U) := by
  induction l with
  | zero => simpa only [iteratedDeriv_zero] using hg
  | succ l ih =>
    have h := holomorphicSlice_deriv_smooth hS hU ih
      (fun p hp => Holomorphic.DerivativeApproximation.Dolbeault.holomorphic_iteratedDeriv_on (hhol p hp) hU l)
    simpa only [iteratedDeriv_succ] using h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.HolomorphicSliceDerivatives.Dolbeault
