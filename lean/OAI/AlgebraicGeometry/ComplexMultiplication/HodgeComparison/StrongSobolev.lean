import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDerivativeCoordinates
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv

/-! # Strong Sobolev -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction

noncomputable section

section

/-! A recursive description of actual higher L2 derivatives using strong
limits of spatial difference quotients. This works for real Hilbert-valued
fields, including coefficient fields acting real-linearly on complex vectors. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology SchwartzMap

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fintype ι]

/-- Strong L2 directional derivatives through order n. The difference bounds
record the usual uniform first-order Sobolev estimate. -/
def HasStrongSobolevDerivatives (b : OrthonormalBasis ι ℝ E) :
    ℕ → Lp F 2 (volume : Measure E) → Prop
  | 0, _ => True
  | n + 1, u => HasStrongSobolevDerivatives b n u ∧
      ∀ i : ι, ∃ v : Lp F 2 (volume : Measure E),
        Tendsto (fun t : ℝ => DifferenceProduct.CM.Construction.realL2Difference (b i) t u) (𝓝[≠] 0) (𝓝 v) ∧
        (∃ B : ℝ, ∀ t, ‖DifferenceProduct.CM.Construction.realL2Difference (b i) t u‖ ≤ B) ∧
        HasStrongSobolevDerivatives b n v

theorem strongSobolev_zero (b : OrthonormalBasis ι ℝ E) (n : ℕ) :
    Construction.HasStrongSobolevDerivatives b n (0 : Lp F 2 (volume : Measure E)) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih, fun i => ⟨0, ?_, ⟨0, fun t => by simp⟩, ih⟩⟩
    simpa only [map_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : Lp F 2 (volume : Measure E))) (𝓝[≠] 0) (𝓝 0))

theorem HasStrongSobolevDerivatives.of_succ (b : OrthonormalBasis ι ℝ E) {n : ℕ}
    {u : Lp F 2 (volume : Measure E)} (hu : Construction.HasStrongSobolevDerivatives b (n + 1) u) :
    Construction.HasStrongSobolevDerivatives b n u := hu.1

theorem HasStrongSobolevDerivatives.mono (b : OrthonormalBasis ι ℝ E) {m n : ℕ}
    (hmn : m ≤ n) {u : Lp F 2 (volume : Measure E)} (hu : Construction.HasStrongSobolevDerivatives b n u) :
    Construction.HasStrongSobolevDerivatives b m u := by
  induction n with
  | zero => simpa only [Nat.le_zero.mp hmn] using hu
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hmn with h | h
    · exact h ▸ hu
    · exact ih (Nat.lt_succ_iff.mp h) hu.1

theorem HasStrongSobolevDerivatives.add (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    {u v : Lp F 2 (volume : Measure E)} (hu : Construction.HasStrongSobolevDerivatives b n u)
    (hv : Construction.HasStrongSobolevDerivatives b n v) : Construction.HasStrongSobolevDerivatives b n (u + v) := by
  induction n generalizing u v with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih hu.1 hv.1, fun i => ?_⟩
    obtain ⟨du, hdu, ⟨Bu, hBu⟩, hduN⟩ := hu.2 i
    obtain ⟨dv, hdv, ⟨Bv, hBv⟩, hdvN⟩ := hv.2 i
    refine ⟨du + dv, ?_, ⟨Bu + Bv, fun t => ?_⟩, ih hduN hdvN⟩
    · simpa only [map_add] using hdu.add hdv
    · rw [map_add]
      exact (norm_add_le _ _).trans (add_le_add (hBu t) (hBv t))

theorem HasStrongSobolevDerivatives.smul (b : OrthonormalBasis ι ℝ E) (n : ℕ) (r : ℝ)
    {u : Lp F 2 (volume : Measure E)} (hu : Construction.HasStrongSobolevDerivatives b n u) :
    Construction.HasStrongSobolevDerivatives b n (r • u) := by
  induction n generalizing u with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih hu.1, fun i => ?_⟩
    obtain ⟨du, hdu, ⟨B, hB⟩, hduN⟩ := hu.2 i
    refine ⟨r • du, ?_, ⟨‖r‖ * B, fun t => ?_⟩, ih hduN⟩
    · simpa only [map_smul] using hdu.const_smul r
    · rw [map_smul, norm_smul]
      exact mul_le_mul_of_nonneg_left (hB t) (norm_nonneg _)

theorem HasStrongSobolevDerivatives.neg (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    {u : Lp F 2 (volume : Measure E)} (hu : Construction.HasStrongSobolevDerivatives b n u) :
    Construction.HasStrongSobolevDerivatives b n (-u) := by
  simpa only [neg_one_smul] using hu.smul b n (-1)

end

/-! The recursive strong-derivative description is equivalent to the native
distributional Sobolev regularity for the actual complex-valued L2 functions. -/

open _root_.MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap LineDeriv _root_.Topology

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

theorem strongSobolev_succ_is_h1 (b : OrthonormalBasis ι ℝ E) {n : ℕ}
    {u : Lp ℂ 2 (volume : Measure E)} (hu : Construction.HasStrongSobolevDerivatives b (n + 1) u) :
    MemSobolev 1 2 (u : 𝓢'(E, ℂ)) := by
  apply DifferenceCriterion.CM.Construction.memSobolev_one_of_difference_bounds b
  intro i
  obtain ⟨_, _, ⟨B, hB⟩, _⟩ := hu.2 i
  refine ⟨B, Filter.Eventually.of_forall (fun t => ?_)⟩
  rw [← DifferenceProduct.CM.Construction.realL2Difference_eq_complex]
  exact hB t

theorem strongSobolev_iff_memSobolev (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (u : Lp ℂ 2 (volume : Measure E)) :
    Construction.HasStrongSobolevDerivatives b n u ↔ MemSobolev (n : ℝ) 2 (u : 𝓢'(E, ℂ)) := by
  induction n generalizing u with
  | zero =>
    simp only [Nat.cast_zero, Construction.HasStrongSobolevDerivatives, true_iff]
    exact memSobolev_zero_iff.mpr ⟨u, rfl⟩
  | succ n ih =>
    constructor
    · intro hu
      obtain ⟨w, hw⟩ := (SobolevDerivativeCoordinates.CM.Construction.memSobolev_l2_iff_embedding_range (by norm_num : (0 : ℝ) ≤ 1) u).mp
        (strongSobolev_succ_is_h1 b hu)
      rw [Nat.cast_succ]
      apply (SobolevInv.CM.Construction.memSobolev_succ_iff_derivatives b (n : ℝ) (u : 𝓢'(E, ℂ))).mpr
      refine ⟨(ih u).mp hu.1, fun i => ?_⟩
      obtain ⟨du, hdu, _, hduN⟩ := hu.2 i
      have hknown := DifferenceConvergence.CM.Construction.l2DifferenceQuotient_tendsto_derivative (b i) w
      rw [hw] at hknown
      have hdu' : Tendsto (fun t : ℝ => DifferenceQuotients.CM.Construction.l2DifferenceQuotient (b i) t u) (𝓝[≠] 0) (𝓝 du) := by
        simpa only [DifferenceProduct.CM.Construction.realL2Difference_eq_complex] using hdu
      have heq := tendsto_nhds_unique hdu' hknown
      have hdistr : (du : 𝓢'(E, ℂ)) = ∂_{b i} (u : 𝓢'(E, ℂ)) := by
        rw [heq, SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution, hw]
      rw [← hdistr]
      exact (ih du).mp hduN
    · intro hu
      have hu1 : MemSobolev 1 2 (u : 𝓢'(E, ℂ)) :=
        hu.mono (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      obtain ⟨w, hw⟩ := (SobolevDerivativeCoordinates.CM.Construction.memSobolev_l2_iff_embedding_range (by norm_num : (0 : ℝ) ≤ 1) u).mp hu1
      rw [Nat.cast_succ] at hu
      have hp := (SobolevInv.CM.Construction.memSobolev_succ_iff_derivatives b (n : ℝ) (u : 𝓢'(E, ℂ))).mp hu
      refine ⟨(ih u).mpr hp.1, fun i =>
        ⟨SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) w, ?_, ⟨(2 * Real.pi * ‖b i‖) * ‖w‖, fun t => ?_⟩, ?_⟩⟩
      · simpa only [DifferenceProduct.CM.Construction.realL2Difference_eq_complex, hw] using
          DifferenceConvergence.CM.Construction.l2DifferenceQuotient_tendsto_derivative (b i) w
      · rw [DifferenceProduct.CM.Construction.realL2Difference_eq_complex, ← hw]
        exact DifferenceBounds.CM.Construction.l2DifferenceQuotient_sobolev_bound (b i) t w
      · apply (ih _).mpr
        rw [SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution, hw]
        exact hp.2 i

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction
