import OAI.Analysis.PDE.Concentration.Normalization
import OAI.Analysis.PDE.Concentration.Packet.L2
import OAI.Analysis.PDE.Concentration.Input.Integrability

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current

theorem physicalSpatialCell_volume_pos {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) :
    0 < volume.real (physicalSpatialCell R) := by
  rw [physicalSpatialCell_volume]
  let e : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d :=
    R.trans ((LinearEquiv.smulOfNeZero ℝ (OAI.Analysis.Calculus.Current.SpatialSpace d) 100 (by norm_num)).toContinuousLinearEquiv)
  exact abs_pos.mpr e.toLinearEquiv.isUnit_det'.ne_zero

/-- Supremum normalization controls every Fourier coefficient, on every
full rotated side-100 lattice; this is derived from exact Parseval. -/
theorem packet_coefficient_le_one {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ)
    (hinj : Function.Injective m)
    (hm : ∀ j i, inner ℝ (packetSpatialFrequency (κ j) (v j)) (R (EuclideanSpace.single i 1)) =
      (m j i : ℝ) * (2 * Real.pi) / 100)
    (hnorm : ∀ y, ‖packetBaseWave κ cR cI v 0 y‖ ≤ 1) (k : ι) :
    ‖(⟨cR k, cI k⟩ : ℂ)‖ ≤ 1 := by
  have hfinite : volume (physicalSpatialCell R) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedPhysicalSpatialCell R).measure_ne_top
      (measure_mono (physicalSpatialCell_subset_closed R))
  have hi : Integrable (fun _ : OAI.Analysis.Calculus.Current.SpatialSpace d => (1 : ℝ)) (volume.restrict (physicalSpatialCell R)) :=
    integrableOn_const hfinite
  have hb := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun y => sq_nonneg ‖packetBaseWave κ cR cI v 0 y‖) hi
    (Filter.Eventually.of_forall fun y => by nlinarith [hnorm y, norm_nonneg (packetBaseWave κ cR cI v 0 y)])
  rw [integral_sq_packetBaseWave R κ cR cI v m hinj hm 0, integral_const] at hb
  simp only [smul_eq_mul, mul_one, measureReal_restrict_apply_univ] at hb
  rw [← physicalSpatialCell_volume] at hb
  have hsum : (∑ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ^ 2) ≤ 1 := by
    nlinarith [physicalSpatialCell_volume_pos R]
  have hk := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg ‖(⟨cR j, cI j⟩ : ℂ)‖)
    (Finset.mem_univ k)
  nlinarith [norm_nonneg (⟨cR k, cI k⟩ : ℂ)]

theorem compact_packet_frequency_bound {d : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)} (hK : IsCompact K) :
    ∃ F : ℝ, 0 < F ∧ ∀ {h κ : ℝ} (v : Fin d → ℝ), 0 < h → 0 < κ →
      h • packetSpatialFrequency κ v ∈ K → κ ≤ F / h := by
  obtain ⟨D, hD⟩ := (hK.image continuous_gaussianFrequencyK).isBounded.exists_norm_le
  refine ⟨max D 0 + 1, by positivity, ?_⟩
  intro h κ v hh hκ hf
  have hb := hD _ (Set.mem_image_of_mem gaussianFrequencyK hf)
  rw [gaussianFrequencyK_smul hh.le, gaussianFrequencyK_packet hκ.le] at hb
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hh hκ)] at hb
  apply (le_div_iff₀ hh).mpr
  nlinarith [le_max_left D 0]

theorem packet_velocity_bound {d : ℕ} {h κ : ℝ} (v : Fin d → ℝ)
    (hh : 0 < h) (hκ : 0 < κ)
    (hv : ‖gaussianVelocity (h • packetSpatialFrequency κ v)‖ ≤ 1 / 40) :
    (∑ i, |v i| ^ 2) ≤ 1 / 1600 := by
  rw [gaussianVelocity_smul hh.ne' hh.le] at hv
  have he : ‖gaussianVelocity (packetSpatialFrequency κ v)‖ ^ 2 = ∑ i, |v i| ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [gaussianVelocity_packet_apply hκ, Complex.norm_real, Real.norm_eq_abs]
  nlinarith [norm_nonneg (gaussianVelocity (packetSpatialFrequency κ v))]

end OAI.Analysis.PDE.Concentration
