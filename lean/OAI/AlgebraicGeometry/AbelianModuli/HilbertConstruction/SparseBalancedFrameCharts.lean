import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.ChartDenominators
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingMonomialCompletion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.IndexedProjectiveFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantAlgebra

/-! # Sparse Balanced Frame Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseBalancedFrameCharts

noncomputable section

/-! Sparsity produces a frame and a nonvanishing balanced denominator.
Every normalized coordinate has an explicit balancing complement. -/
open scoped BigOperators Classical
universe u
variable {K : Type u} [Field K] {r m : ℕ}

theorem sparseConfiguration_exists_frame_discriminant
    (v : Fin m → Fin r → K) (hr : 0 < r)
    (hs : ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => v i ∈ W)).card < m) :
    ∃ (σ : Fin r → Fin m) (e : Fin m),
      IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun K (Fin r)) (fun j => v (σ j)) (v e)) := by
  have hdim : Module.finrank K (Fin r → K) = r := by simp
  have hf := SparseFiniteProjectiveFrames.sparseFiniteFamily_projectiveFrame v (hdim.symm ▸ hr)
    (by simpa only [hdim, Fintype.card_fin] using hs)
  obtain ⟨b, σ, hb, e, he⟩ := Finite.IndexedProjectiveFrames.hasFiniteIndexedProjectiveFrame_of_basis v hdim hf
  refine ⟨σ, e, (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant_isUnit_iff _ _ _).mpr ?_⟩
  exact ⟨b, hb, fun k => isUnit_iff_ne_zero.mpr (he k)⟩

theorem sparseConfiguration_balanced_frame_chart
    (v : Fin m → Fin r → K) (hv : ∀ i, v i ≠ 0) (hr : 2 ≤ r) (hm : 2 ≤ m)
    (hs : ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => v i ∈ W)).card < m) :
    ∃ (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
      (a : (Fin r → Fin m) → ℕ) (C : Fin m → (Fin r → Fin m) → ℕ),
      a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight ∧
      Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) a ≠ 0 ∧
      Frame.ChartDenominators.frameChartExponent σ e c ≤ a ∧
      (∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a) ∧
      (∀ z k, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z k ∈
        Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) ∧
      ∀ i : Fin m, 0 < Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i := by
  obtain ⟨σ, e, hframe⟩ := sparseConfiguration_exists_frame_discriminant v (by omega) hs
  obtain ⟨c, hc⟩ := Frame.ChartDenominators.frame_exists_nonvanishing_chart v hv σ e hframe
  obtain ⟨a, b, ha, hab, han⟩ := NonvanishingMonomialCompletion.sparseConfiguration_complete_nonvanishing_monomial
    v hv hr hm hs (Frame.ChartDenominators.frameChartExponent σ e c) hc
  have hle : Frame.ChartDenominators.frameChartExponent σ e c ≤ a := by
    rw [← hab]
    intro τ
    exact Nat.le_add_left _ _
  have hC (z : Fin m) : ∃ C, C + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a :=
    SupportedExponentCompletion.exponent_complement_of_le ((Frame.ChartDenominators.frameCoordinateExponent_le_chart σ e z c).trans hle)
  choose C hC using hC
  refine ⟨σ, e, c, a, C, ha, han, hle, hC, ?_, ?_⟩
  · intro z k
    exact Balanced.ExponentCompletion.balanced_completion_of_same_degree DeterminantBlockDegrees.labeledDeterminantWeight a
      (Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z)) (C z) (Frame.CoordinateExponents.frameCoordinateExponent σ e z k)
      ha (hC z) (Frame.CoordinateExponents.frameCoordinateExponent_degrees_equal σ e z k (c z))
  · intro i
    have hσ : 0 < Frame.ChartDenominators.frameDiscriminantExponent σ e σ := by
      simp only [Frame.ChartDenominators.frameDiscriminantExponent, Pi.add_apply, Pi.single_eq_same]
      omega
    have hapos : 0 < a σ := hσ.trans_le ((Frame.ChartDenominators.frameDiscriminantExponent_le_chart σ e c).trans hle σ)
    apply Nat.pos_of_ne_zero
    intro hz
    have ha0 := (Balanced.DeterminantAlgebra.balancedDeterminantMonomial_degree_zero_iff (by omega) a ha i).mp hz
    exact (Nat.ne_of_gt hapos) (congrFun ha0 σ)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseBalancedFrameCharts
