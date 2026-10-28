import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ParameterCircleIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Contour Derivative -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ContourDerivative.Dolbeault

noncomputable section

section

/-! The original parameter derivative of a smooth contour-integral
family, defined by restriction of its actual joint Fréchet derivative. -/

open Set _root_.Metric
open scoped _root_.Topology ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def circleParameterDerivative (g : P × ℂ → F) (q : P × ℂ) : P →L[ℝ] F :=
  (fderiv ℝ g q).comp (ContinuousLinearMap.inl ℝ P ℂ)

theorem circleParameterDerivative_smooth {g : P × ℂ → F} {W : Set (P × ℂ)}
    (hW : IsOpen W) (hg : ContDiffOn ℝ ∞ g W) :
    ContDiffOn ℝ ∞ (circleParameterDerivative g) W :=
  (hg.fderiv_of_isOpen hW (m := ∞) (by simp)).clm_comp contDiffOn_const

variable [FiniteDimensional ℝ P] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem hasFDerivAt_circleIntegral_of_smooth {g : P × ℂ → F} {W : Set (P × ℂ)}
    (hW : IsOpen W) (hg : ContDiffOn ℝ ∞ g W) {S : Set P} (hS : IsOpen S)
    {p : P} (hp : p ∈ S) {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hSW : S ×ˢ sphere c r ⊆ W) :
    HasFDerivAt (fun q => circleIntegral (fun z => g (q, z)) c r)
      (circleIntegral (fun z => circleParameterDerivative g (p, z)) c r) p := by
  apply ParameterCircleIntegral.Dolbeault.hasFDerivAt_parameter_circleIntegral (g := fun q z => g (q, z))
    (g' := fun q z => circleParameterDerivative g (q, z)) hS hp hr
    (hg.continuousOn.mono hSW) ((circleParameterDerivative_smooth hW hg).continuousOn.mono hSW)
  intro q hq z hz
  exact ((hg.contDiffAt (hW.mem_nhds (hSW ⟨hq, hz⟩))).differentiableAt (by simp)).hasFDerivAt.comp q
    (hasFDerivAt_prodMk_left q z)

end

/-! Smooth parameter dependence of the actual contour integral, proved
by repeated differentiation under the integral in the operator-valued codomain. -/

open Set _root_.Metric
open scoped ContDiff

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem contDiffOn_circleIntegral_nat (n : ℕ)
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] {g : P × ℂ → F} {W : Set (P × ℂ)}
    (hW : IsOpen W) (hg : ContDiffOn ℝ ∞ g W) {S : Set P} (hS : IsOpen S)
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hSW : S ×ˢ sphere c r ⊆ W) :
    ContDiffOn ℝ n (fun p => circleIntegral (fun z => g (p, z)) c r) S := by
  induction n generalizing F with
  | zero =>
    apply contDiffOn_zero.mpr
    intro p hp
    exact (hasFDerivAt_circleIntegral_of_smooth hW hg hS hp hr hSW).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS.uniqueDiffOn).mpr
    refine ⟨by simp, fun p => circleIntegral (fun z => circleParameterDerivative g (p, z)) c r,
      ih (circleParameterDerivative_smooth hW hg), ?_⟩
    intro p hp
    exact (hasFDerivAt_circleIntegral_of_smooth hW hg hS hp hr hSW).hasFDerivWithinAt

theorem contDiffOn_circleIntegral_smooth
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] {g : P × ℂ → F} {W : Set (P × ℂ)}
    (hW : IsOpen W) (hg : ContDiffOn ℝ ∞ g W) {S : Set P} (hS : IsOpen S)
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hSW : S ×ˢ sphere c r ⊆ W) :
    ContDiffOn ℝ ∞ (fun p => circleIntegral (fun z => g (p, z)) c r) S :=
  contDiffOn_infty.mpr (fun n => contDiffOn_circleIntegral_nat n hW hg hS hr hSW)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ContourDerivative.Dolbeault
