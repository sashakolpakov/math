import OAI.Analysis.Fourier.WavePackets.AngularCompact

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration
open scoped ContDiff ENNReal FourierTransform

/-- The actual finite angular decomposition. Its number of pieces has
the sharp sphere dimension, its inverse-kernel norms are uniform, and
all rotated frequencies lie in one fixed compact positive packet set. -/
theorem uniform_angular_partition {d : ℕ} {φ : Space (d + 1) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ Ccount Ckernel γ₀ : ℝ, ∃ K : Set (OAI.Analysis.Calculus.Current.SpatialSpace d),
      0 < Ccount ∧ 0 ≤ Ckernel ∧ 0 < γ₀ ∧ IsCompact K ∧
      (∀ η ∈ K, 0 < OAI.Analysis.PDE.Concentration.gaussianFrequencyK η) ∧
      (∀ η ∈ K, ‖OAI.Analysis.PDE.Concentration.gaussianVelocity η‖ ≤ 1 / 40) ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
        ∃ (I : Type) (_ : Fintype I) (ψ : I → Space (d + 1) → ℂ)
          (R : I → Space (d + 1) ≃ₗᵢ[ℝ] Space (d + 1)),
          (Fintype.card I : ℝ) ≤ Ccount * (γ⁻¹) ^ d ∧
          (fun ξ => ∑ i : I, ψ i ξ) = φ ∧
          ∀ i, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧
            tsupport (ψ i) ⊆ tsupport φ ∧
            eLpNorm (𝓕⁻ (ψ i)) 1 volume ≤ ENNReal.ofReal Ckernel ∧
            ∀ ξ ∈ tsupport (ψ i),
              (OAI.Analysis.PDE.Concentration.spatialFinIsometry d).symm (R i ξ) ∈ K ∧
              ‖OAI.Analysis.PDE.Concentration.gaussianVelocity ((OAI.Analysis.PDE.Concentration.spatialFinIsometry d).symm (R i ξ))‖ ≤ 4 * d * γ := by
  classical
  obtain ⟨s, b, a, hb, hsum⟩ := finite_angular_atlas hφ hc hz
  obtain ⟨a₀, ha₀, ha₀le⟩ := finite_positive_lower_bound a (fun i => (hb i).2.2.1)
  obtain ⟨B, hB, hbound⟩ := hc.isBounded.exists_pos_norm_le
  choose r C hr hC hpart using fun i : s =>
    angular_chart_partition (hb i).1 (hb i).2.1 (hb i).2.2.1 (hb i).2.2.2.1
  let Ccount : ℝ := 1 + ∑ i : s, (2 * r i + 3) ^ d
  let Ckernel : ℝ := ∑ i : s, C i
  let γ₀ : ℝ := (160 * ((d : ℝ) + 1))⁻¹
  let K := angularPacketCompact d (a₀ / 2) B
  have hcount : 0 < Ccount := by
    have hh : 0 ≤ ∑ i : s, (2 * r i + 3) ^ d :=
      Finset.sum_nonneg (fun i _ => pow_nonneg (by linarith [hr i]) d)
    exact add_pos_of_pos_of_nonneg zero_lt_one hh
  refine ⟨Ccount, Ckernel, γ₀, K, hcount, Finset.sum_nonneg (fun i _ => hC i),
    by dsimp [γ₀]; positivity, isCompact_angularPacketCompact _ _ _,
    fun η hη => angularPacketCompact_positive (by positivity) hη,
    fun η hη => angularPacketCompact_velocity (by positivity) hη, ?_⟩
  intro γ hγ hγ₀
  have hd0 : 0 ≤ (d : ℝ) := by positivity
  have hden : 0 < 160 * ((d : ℝ) + 1) := by positivity
  have hscale : γ * (160 * ((d : ℝ) + 1)) ≤ 1 := by
    apply (le_div_iff₀ hden).mp
    simpa only [one_div] using hγ₀
  have hγ1 : γ ≤ 1 := by nlinarith
  have hsmall : (d : ℝ) * γ ≤ 1 / 2 := by nlinarith
  have hvelsmall : 4 * (d : ℝ) * γ ≤ 1 / 40 := by nlinarith
  let J := fun i : s => Fin d → Fin (2 * angularGridSize (r i) γ + 1)
  let I := (i : s) × J i
  let χ := fun (i : s) (k : J i) => angularChartSymbol (b i) γ (angularGridCenter (r i) γ k)
  let ψ : I → Space (d + 1) → ℂ := fun j ξ => χ j.1 j.2 (j.1.val ξ)
  let R : I → Space (d + 1) ≃ₗᵢ[ℝ] Space (d + 1) := fun j =>
    j.1.val.trans (angularChartRotation (angularGridCenter (r j.1) γ j.2))
  have hj (i : s) := hpart i γ hγ hγ1
  change ∀ i : s,
    (Fintype.card (J i) : ℝ) ≤ ((2 * r i + 3) / γ) ^ d ∧
      (fun ξ => ∑ k : J i, χ i k ξ) = b i ∧
      ∀ k : J i, ContDiff ℝ ∞ (χ i k) ∧ HasCompactSupport (χ i k) ∧
        tsupport (χ i k) ⊆ tsupport (b i) ∧
        eLpNorm (𝓕⁻ (χ i k)) 1 volume ≤ ENNReal.ofReal (C i) ∧
        ∀ ξ ∈ tsupport (χ i k), ∀ l : Fin d,
          |ξ l.succ - angularGridCenter (r i) γ k l * ξ 0| ≤ γ * ξ 0 at hj
  refine ⟨I, inferInstance, ψ, R, ?_, ?_, ?_⟩
  · have he : (Fintype.card I : ℝ) = ∑ i : s, (Fintype.card (J i) : ℝ) := by
      simp [I, Fintype.card_sigma]
    rw [he]
    calc
      _ ≤ ∑ i : s, ((2 * r i + 3) / γ) ^ d := Finset.sum_le_sum (fun i _ => (hj i).1)
      _ = (∑ i : s, (2 * r i + 3) ^ d) * (γ⁻¹) ^ d := by
        simp_rw [div_eq_mul_inv, mul_pow]
        rw [Finset.sum_mul]
      _ ≤ Ccount * (γ⁻¹) ^ d := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [Ccount]
        linarith
  · funext ξ
    change (∑ j : (i : s) × J i, χ j.1 j.2 (j.1.val ξ)) = φ ξ
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ i : s, b i (i.val ξ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrFun (hj i).2.1 (i.val ξ)
      _ = φ ξ := congrFun hsum ξ
  · rintro ⟨i, k⟩
    have hdata := (hj i).2.2 k
    have hsψ : tsupport (ψ ⟨i, k⟩) ⊆ tsupport φ := by
      intro ξ hξ
      have hx : i.val ξ ∈ tsupport (χ i k) :=
        tsupport_comp_subset_preimage (χ i k) i.val.continuous hξ
      have hx' := hdata.2.2.1 hx
      have hbpre : ξ ∈ tsupport (fun x => b i (i.val x)) := by
        change ξ ∈ tsupport (b i ∘ i.val.toHomeomorph)
        rw [tsupport_comp_eq_preimage]
        exact hx'
      exact (hb i).2.2.2.2 hbpre
    refine ⟨hdata.1.comp i.val.contDiff,
      hdata.2.1.comp_homeomorph i.val.toHomeomorph, hsψ, ?_, ?_⟩
    · have he : eLpNorm (𝓕⁻ (ψ ⟨i, k⟩)) 1 volume =
          eLpNorm (𝓕⁻ (χ i k)) 1 volume :=
        eLpNorm_fourierInv_comp_smooth hdata.1 hdata.2.1 i.val.toContinuousLinearEquiv
      rw [he]
      apply hdata.2.2.2.1.trans
      apply ENNReal.ofReal_le_ofReal
      exact Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
    · intro ξ hξ
      have hx : i.val ξ ∈ tsupport (χ i k) :=
        tsupport_comp_subset_preimage (χ i k) i.val.continuous hξ
      have hxi : a i ≤ i.val ξ 0 := (hb i).2.2.2.1 _ (hdata.2.2.1 hx)
      have hx0 : 0 < i.val ξ 0 := lt_of_lt_of_le (hb i).2.2.1 hxi
      have hw := hdata.2.2.2.2 (i.val ξ) hx
      have hv := angular_chart_gaussian_velocity_bound hγ.le hsmall
        (angularGridCenter (r i) γ k) hx0 hw
      have hpos := angular_chart_positive_rotated_axis hγ.le hsmall
        (angularGridCenter (r i) γ k) hx0.le hw
      change (OAI.Analysis.PDE.Concentration.spatialFinIsometry d).symm
          (angularChartRotation (angularGridCenter (r i) γ k) (i.val ξ)) ∈ K ∧ _
      refine ⟨mem_angularPacketCompact ?_ ?_ hv.1 (hv.2.trans hvelsmall), hv.2⟩
      · rw [(OAI.Analysis.PDE.Concentration.spatialFinIsometry d).symm.norm_map, (angularChartRotation _).norm_map,
          i.val.norm_map]
        exact hbound ξ (hsψ hξ)
      · simp only [OAI.Analysis.PDE.Concentration.spatialFinIsometry_symm_apply]
        change a₀ / 2 ≤ angularChartRotation (angularGridCenter (r i) γ k) (i.val ξ) 0
        have := ha₀le i
        linarith

end OAI.Analysis.Fourier.WavePackets
