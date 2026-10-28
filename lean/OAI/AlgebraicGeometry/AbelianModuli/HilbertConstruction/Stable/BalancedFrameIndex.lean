import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedFrameCharts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantSparsityPreservation

/-! # Balanced Frame Index -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedFrameIndex

noncomputable section

/-! The stable balanced charts have indices consisting of their finite
frame and exponent data, with a proved fieldwise sparsity condition. -/
open scoped Classical
universe u

structure StableBalancedFrameIndex (r m : ℕ) where
  rank_two : 2 ≤ r
  points_two : 2 ≤ m
  frame : Fin r → Fin m
  additional : Fin m
  coordinate : Fin m → Fin r
  exponent : (Fin r → Fin m) → ℕ
  complement : Fin m → (Fin r → Fin m) → ℕ
  balanced : exponent ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight
  frame_le : Frame.ChartDenominators.frameChartExponent frame additional coordinate ≤ exponent
  complete : ∀ z, complement z + Frame.CoordinateExponents.frameCoordinateExponent frame additional z (coordinate z) = exponent
  sparse : ∀ (K : Type u) [Field K] (w : Fin m → Fin r → K),
    Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) exponent ≠ 0 →
      ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
        r * (Finset.univ.filter (fun z => w z ∈ W)).card < m

theorem StableBalancedFrameIndex.degree_positive {r m : ℕ}
    (j : StableBalancedFrameIndex.{u} r m) (i : Fin m) :
    0 < Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight j.exponent i := by
  have hr : 0 < r := lt_of_lt_of_le (by decide : 0 < 2) j.rank_two
  have hσ : 0 < Frame.ChartDenominators.frameDiscriminantExponent j.frame j.additional j.frame := by
    simp only [Frame.ChartDenominators.frameDiscriminantExponent, Pi.add_apply, Pi.single_eq_same]
    omega
  have hpos : 0 < j.exponent j.frame := hσ.trans_le
    ((Frame.ChartDenominators.frameDiscriminantExponent_le_chart j.frame j.additional j.coordinate).trans j.frame_le j.frame)
  apply Nat.pos_of_ne_zero
  intro hz
  have hzero := (Balanced.DeterminantAlgebra.balancedDeterminantMonomial_degree_zero_iff hr j.exponent j.balanced i).mp hz
  exact (Nat.ne_of_gt hpos) (congrFun hzero j.frame)

theorem sparseConfiguration_has_stableBalancedFrameIndex
    {K : Type u} [Field K] {r m : ℕ}
    (v : Fin m → Fin r → K) (hv : ∀ i, v i ≠ 0) (hr : 2 ≤ r) (hm : 2 ≤ m)
    (hs : ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => v i ∈ W)).card < m) :
    ∃ j : StableBalancedFrameIndex.{u} r m,
      Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) j.exponent ≠ 0 := by
  obtain ⟨σ, e, c, a, C, ha, han, hframe, hC, hapos⟩ :=
    BalancedFrameCharts.sparseConfiguration_stable_balanced_frame_chart v hv hr hm hs
  refine ⟨⟨hr, hm, σ, e, c, a, C, ha, hframe, hC, ?_⟩, han⟩
  intro L hL w hw
  exact DeterminantSparsityPreservation.hyperplaneSparsity_of_nonvanishing_determinant_monomial v w a hapos hw hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedFrameIndex
