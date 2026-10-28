import OAI.Analysis.PDE.Concentration.AngularCutoff
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Metric OAI.Analysis.Calculus.Current
open scoped ContDiff

theorem exists_compact_complex_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : E → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ U ∧
      ∀ x ∈ K, f x = 1 := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨f, hf, hfr, hfs, hfe⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤) hVo hK.isClosed hKV
  have he : tsupport (fun x => (f x : ℂ)) = closure V := by
    unfold tsupport
    congr 1
    ext x
    simpa only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using
      (iff_of_eq (congrArg (x ∈ ·) hfs))
  refine ⟨fun x => (f x : ℂ), ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp hf
  · change IsCompact (tsupport (fun x => (f x : ℂ)))
    rw [he]
    exact hVc
  · exact he ▸ hVU
  · intro x hx
    dsimp only
    rw [(hfe x).mp hx]
    simp

/-- Fixed cutoffs covering a compact positive-frequency patch and a bounded
rescaled angular sector. Neither cutoff depends on the semiclassical scale. -/
theorem exists_sector_cutoffs {d : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η) (R : ℝ) (_ : 0 ≤ R) :
    ∃ (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (χ : TransverseSpace d → ℂ),
      ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) ∧
      (∀ η ∈ K, ρ η = 1) ∧
      (∀ W : TransverseSpace d, ‖W‖ ≤ Real.sqrt 12 * R → χ W = 1) := by
  obtain ⟨ρ, hρ, hcρ, hpρ, heρ⟩ := exists_compact_complex_cutoff hK
    (isOpen_lt continuous_const continuous_gaussianFrequencyK) hpos
  obtain ⟨χ, hχ, hcχ, hpχ, heχ⟩ := exists_compact_complex_cutoff
    (isCompact_closedBall (0 : TransverseSpace d) (Real.sqrt 12 * R))
    (isOpen_ball : IsOpen (ball (0 : TransverseSpace d) (Real.sqrt 12 * R + 1)))
    (closedBall_subset_ball (by linarith))
  refine ⟨ρ, χ, hρ, hcρ, hχ, hcχ, hpρ, heρ, ?_⟩
  intro W hW
  exact heχ W (by simpa only [mem_closedBall, dist_zero_right] using hW)

theorem scaled_sector_cutoff_eq_one {d : ℕ} {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    {χ : TransverseSpace d → ℂ} {R L ℓ : ℝ} (_ : 0 ≤ R) (_ : 0 < L)
    (_ : 0 ≤ ℓ) (hu : ℓ ≤ 12 * L)
    (hχ : ∀ W : TransverseSpace d, ‖W‖ ≤ Real.sqrt 12 * R → χ W = 1)
    {η : OAI.Analysis.Calculus.Current.SpatialSpace d} (hρ : ρ η = 1) (hv : Real.sqrt L * ‖gaussianVelocity η‖ ≤ R) :
    radialAngularCutoff ρ χ (Real.sqrt ℓ) η = 1 := by
  have hs : Real.sqrt ℓ ≤ Real.sqrt 12 * Real.sqrt L := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
    exact Real.sqrt_le_sqrt hu
  have hb : ‖Real.sqrt ℓ • gaussianVelocity η‖ ≤ Real.sqrt 12 * R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ (Real.sqrt 12 * Real.sqrt L) * ‖gaussianVelocity η‖ :=
        mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      _ = Real.sqrt 12 * (Real.sqrt L * ‖gaussianVelocity η‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hv (Real.sqrt_nonneg _)
  simp only [radialAngularCutoff, hρ, hχ _ hb, mul_one]

end OAI.Analysis.PDE.Concentration
