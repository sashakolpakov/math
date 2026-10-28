import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.CauchyPolynomials
import OAI.AlgebraicGeometry.Comparison.Betti.CauchyPolynomialNaturality

/-! # Cauchy Polynomial Directions -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CauchyPolynomialDirections.Dolbeault

noncomputable section

section

/-! Parameter differentiation of the original Cauchy polynomial,
normalized on every actual constant parameter direction. -/

open Set _root_.Metric
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

def realOperatorComplexEvaluation (v : P) : (P →L[ℝ] F) →L[ℂ] F where
  toFun L := L v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (ContinuousLinearMap.apply ℝ F v).continuous

variable [FiniteDimensional ℝ P]

theorem circleParameterDerivative_cauchyParameterPolynomial
    {g : P × ℂ → F} {W : Set (P × ℂ)}
    (hW : IsOpen W) (hg : ContDiffOn ℝ ∞ g W) {S : Set P} (hS : IsOpen S)
    {q : P × ℂ} (hq : q.1 ∈ S) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hSW : S ×ˢ sphere c r ⊆ W) (N : ℕ) :
    Smooth.ContourDerivative.Dolbeault.circleParameterDerivative (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N) q =
      Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial (Smooth.ContourDerivative.Dolbeault.circleParameterDerivative g) c r N q := by
  have hpoly := Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial_smooth hW hg hS hr hSW N
  have hd : DifferentiableAt ℝ (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N) q :=
    (hpoly.contDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hq, mem_univ _⟩)).differentiableAt (by simp)
  have hslice : HasFDerivAt (fun p => Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N (p, q.2))
      (Smooth.ContourDerivative.Dolbeault.circleParameterDerivative (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N) q) q.1 := by
    change HasFDerivAt (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N ∘ fun p => (p, q.2))
      ((fderiv ℝ (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N) q).comp
        (ContinuousLinearMap.inl ℝ P ℂ)) q.1
    exact HasFDerivAt.comp q.1 hd.hasFDerivAt (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2)
  exact hslice.unique (Smooth.CauchyPolynomials.Dolbeault.hasFDerivAt_cauchyParameterPolynomial hW hg hS hq hr hSW N q.2)

theorem cauchyParameterPolynomial_parameter_fderiv [CompleteSpace F]
    {g : P × ℂ → F} {W : Set (P × ℂ)}
    (hW : IsOpen W) (hg : ContDiffOn ℝ ∞ g W) {S : Set P} (hS : IsOpen S)
    {q : P × ℂ} (hq : q.1 ∈ S) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hSW : S ×ˢ sphere c r ⊆ W) (N : ℕ) (v : P) :
    fderiv ℝ (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N) q (v, 0) =
      Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial (fun y => fderiv ℝ g y (v, 0)) c r N q := by
  change Smooth.ContourDerivative.Dolbeault.circleParameterDerivative (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N) q v = _
  rw [circleParameterDerivative_cauchyParameterPolynomial hW hg hS hq hr hSW N]
  have hc : ContinuousOn (fun z => Smooth.ContourDerivative.Dolbeault.circleParameterDerivative g (q.1, z)) (sphere c r) :=
    (Smooth.ContourDerivative.Dolbeault.circleParameterDerivative_smooth hW hg).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun z hz => hSW ⟨hq, hz⟩)
  exact CauchyPolynomialNaturality.Dolbeault.cauchyPowerSeries_partialSum_map (realOperatorComplexEvaluation v) hr hc N q.2

end

/-! The actual Cauchy polynomial preserves every holomorphic parameter
direction whose defining identity holds on the contour. -/

open Set _root_.Metric _root_.Complex
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
theorem cauchyParameterPolynomial_circle_congr {g h : P × ℂ → F} {q : P × ℂ}
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (he : ∀ z ∈ sphere c r, g (q.1, z) = h (q.1, z)) (N : ℕ) :
    Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N q = Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial h c r N q := by
  unfold Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial FormalMultilinearSeries.partialSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [cauchyPowerSeries_apply, cauchyPowerSeries_apply]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  dsimp only
  rw [he z hz]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
theorem cauchyParameterPolynomial_zero (c : ℂ) (r : ℝ) (N : ℕ) (q : P × ℂ) :
    Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial (fun _ => (0 : F)) c r N q = 0 := by
  simp only [Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial, FormalMultilinearSeries.partialSum,
    cauchyPowerSeries_apply, smul_zero, circleIntegral, intervalIntegral.integral_zero,
    Finset.sum_const_zero]

variable [FiniteDimensional ℝ P] [CompleteSpace F] [NormedSpace ℂ P]

theorem cauchyParameterPolynomial_preserves_holomorphic_direction
    {g : P × ℂ → F} {W : Set (P × ℂ)}
    (hW : IsOpen W) (hg : ContDiffOn ℝ ∞ g W) {S : Set P} (hS : IsOpen S)
    {q : P × ℂ} (hq : q.1 ∈ S) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hSW : S ×ˢ sphere c r ⊆ W) (N : ℕ) (v : P)
    (hv : ∀ z ∈ sphere c r, fderiv ℝ g (q.1, z) (I • v, 0) =
      I • fderiv ℝ g (q.1, z) (v, 0)) :
    fderiv ℝ (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N) q (I • v, 0) =
      I • fderiv ℝ (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N) q (v, 0) := by
  let B : (P →L[ℝ] F) →L[ℂ] F :=
    realOperatorComplexEvaluation (I • v) - I • realOperatorComplexEvaluation v
  have hc : ContinuousOn (fun z => Smooth.ContourDerivative.Dolbeault.circleParameterDerivative g (q.1, z)) (sphere c r) :=
    (Smooth.ContourDerivative.Dolbeault.circleParameterDerivative_smooth hW hg).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun z hz => hSW ⟨hq, hz⟩)
  have hmap : B (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial (Smooth.ContourDerivative.Dolbeault.circleParameterDerivative g) c r N q) =
      Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial (fun y => B (Smooth.ContourDerivative.Dolbeault.circleParameterDerivative g y)) c r N q :=
    CauchyPolynomialNaturality.Dolbeault.cauchyPowerSeries_partialSum_map B hr hc N q.2
  have hz : Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial (fun y => B (Smooth.ContourDerivative.Dolbeault.circleParameterDerivative g y)) c r N q = 0 := by
    rw [cauchyParameterPolynomial_circle_congr hr.le (h := fun _ => (0 : F)) ?_ N,
      cauchyParameterPolynomial_zero]
    intro z hz
    change fderiv ℝ g (q.1, z) (I • v, 0) - I • fderiv ℝ g (q.1, z) (v, 0) = 0
    exact sub_eq_zero.mpr (hv z hz)
  have hzero : B (Smooth.ContourDerivative.Dolbeault.circleParameterDerivative (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N) q) = 0 := by
    rw [circleParameterDerivative_cauchyParameterPolynomial hW hg hS hq hr hSW N, hmap, hz]
  exact sub_eq_zero.mp hzero

end

end OAI.AlgebraicGeometry.Comparison.Betti.CauchyPolynomialDirections.Dolbeault
