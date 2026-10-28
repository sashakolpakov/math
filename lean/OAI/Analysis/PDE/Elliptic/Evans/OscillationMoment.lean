import OAI.Analysis.PDE.Elliptic.Evans.MomentPoint

open Set _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

/-- Small-exponent Harnack moments and a finite-direction comparison imply
a strict contraction of oscillation. All constants precede the functions. -/
theorem oscillation_contraction_of_moments {X I : Type*} [MeasurableSpace X]
    [Fintype I] [Nonempty I] {p H δ C E : ℝ}
    (hp : 0 < p) (hH : 0 < H) (hδ : 0 < δ) (hC : 0 < C) (hE : 0 ≤ E) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ (μ : Measure X) (S : Set X), MeasurableSet S → μ S ≠ 0 → μ S ≠ ∞ →
      ∀ (v : I → X → ℝ) (d : I → ℝ) (r small large : ℝ),
      0 < r → (∀ i, 0 ≤ d i) → (∀ i, Measurable (v i)) →
      (∀ i x, x ∈ S → 0 ≤ v i x) →
      (∀ i, (∫⁻ x in S, ENNReal.ofReal (v i x) ^ p ∂μ) ≤
        ENNReal.ofReal (H * (d i + r) ^ p) * μ S) →
      (∀ y ∈ S, δ * small ≤ C * (∑ i, v i y) + E * r) →
      (∑ i, d i) ≤ large - small → small ≤ θ * large + r := by
  classical
  obtain ⟨K, hK, hpoint⟩ := finite_rpow_moments_common_point (X := X) (I := I) hp hH
  let N : ℝ := Fintype.card I
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card I)
  let A := (C * N * K + E) / δ
  have hA : 0 < A := div_pos (by positivity) hδ
  let θ := A / (1 + A)
  have hθ : 0 < θ := div_pos hA (by positivity)
  have hθ1 : θ < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  refine ⟨θ, hθ, hθ1, ?_⟩
  intro μ S hS hμ0 hμfin v d r small large hr hd hv hnonneg hmom hcomp hdiff
  let D := (∑ i, d i) + r
  have hsumd : 0 ≤ ∑ i, d i := Finset.sum_nonneg (fun i _ ↦ hd i)
  have hD : 0 < D := by dsimp [D]; linarith
  have hrD : r ≤ D := by dsimp [D]; linarith
  have hdi (i : I) : d i + r ≤ D := by
    have h := Finset.single_le_sum (fun j _ ↦ hd j) (Finset.mem_univ i)
    dsimp [D]
    linarith
  have hmomD (i : I) : (∫⁻ x in S, ENNReal.ofReal (v i x) ^ p ∂μ) ≤
      ENNReal.ofReal (H * D ^ p) * μ S := by
    apply (hmom i).trans
    apply mul_le_mul_of_nonneg_right _ zero_le
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith [hd i]) (hdi i) hp.le) hH.le
  obtain ⟨y, hy, hyv⟩ := hpoint μ S hS hμ0 hμfin D hD v hv hnonneg hmomD
  have hvsum : (∑ i, v i y) ≤ N * (K * D) := by
    calc
      _ ≤ ∑ _i : I, K * D := Finset.sum_le_sum (fun i _ ↦ hyv i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, N]
  have hraw : δ * small ≤ (C * N * K + E) * D := by
    have hc := hcomp y hy
    have hcv := mul_le_mul_of_nonneg_left hvsum hC.le
    have he := mul_le_mul_of_nonneg_left hrD hE
    nlinarith
  have hcontrol : small ≤ A * D := by
    calc
      small ≤ ((C * N * K + E) * D) / δ :=
        (le_div_iff₀ hδ).mpr (by nlinarith [hraw])
      _ = A * D := by dsimp [A]; ring
  have hcontrol' : small ≤ A * (large - small + r) := by
    apply hcontrol.trans
    apply mul_le_mul_of_nonneg_left _ hA.le
    dsimp [D]
    linarith
  have hlast : small ≤ θ * (large + r) := by
    dsimp [θ]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 1 + A)).mpr
    nlinarith
  apply hlast.trans
  nlinarith [mul_le_mul_of_nonneg_right hθ1.le hr.le]

end OAI.Analysis.PDE.Elliptic
