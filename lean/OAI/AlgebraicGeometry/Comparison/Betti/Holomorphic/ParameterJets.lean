import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ParameterDerivatives

/-! # Parameter Jets -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ParameterJets.Dolbeault

noncomputable section

/-! All evaluated actual iterated real Fréchet derivatives of a smooth
holomorphic family remain holomorphic in its complex-line variable. -/

open Set
open scoped _root_.Topology ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]

omit [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
theorem iteratedDerivative_smooth_on {g : P × ℂ → F} {S : Set P} {U : Set ℂ}
    (hS : IsOpen S) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g (S ×ˢ U)) (k : ℕ) :
    ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k g) (S ×ˢ U) := by
  intro q hq
  exact ((hg.contDiffAt ((hS.prod hU).mem_nhds hq)).iteratedFDeriv_right
    (m := ∞) (WithTop.coe_le_coe.mpr (le_top : (⊤ : ℕ∞) + (k : ℕ∞) ≤ ⊤))).contDiffWithinAt

omit [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
theorem iteratedDerivativeValue_smooth_on {g : P × ℂ → F} {S : Set P} {U : Set ℂ}
    (hS : IsOpen S) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g (S ×ˢ U))
    (k : ℕ) (v : Fin k → P × ℂ) :
    ContDiffOn ℝ ∞ (fun q => iteratedFDeriv ℝ k g q v) (S ×ˢ U) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => P × ℂ) F v).contDiff.comp_contDiffOn
    (iteratedDerivative_smooth_on hS hU hg k)

theorem holomorphicSlice_iteratedDerivative {g : P × ℂ → F} {S : Set P} {U : Set ℂ}
    (hS : IsOpen S) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g (S ×ˢ U))
    (hhol : ∀ p ∈ S, DifferentiableOn ℂ (fun z => g (p, z)) U) (k : ℕ) :
    ∀ (v : Fin k → P × ℂ) (p : P), p ∈ S →
      DifferentiableOn ℂ (fun z => iteratedFDeriv ℝ k g (p, z) v) U := by
  induction k with
  | zero =>
      intro v p hp
      simpa only [iteratedFDeriv_zero_apply] using hhol p hp
  | succ k ih =>
      intro v p hp
      have hInner := iteratedDerivativeValue_smooth_on hS hU hg k (Fin.tail v)
      have hDeriv := ParameterDerivatives.Dolbeault.holomorphicSlice_constantDerivative hS hU hInner (ih (Fin.tail v)) (v 0) hp
      apply hDeriv.congr
      intro z hz
      have hq : (p, z) ∈ S ×ˢ U := ⟨hp, hz⟩
      have hD := (hg.contDiffAt ((hS.prod hU).mem_nhds hq)).differentiableAt_iteratedFDeriv
        (m := k) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
      exact hD.iteratedFDeriv_succ_apply_left'

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ParameterJets.Dolbeault
