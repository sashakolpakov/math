import OAI.Analysis.Fourier.Estimates
import Mathlib.MeasureTheory.Constructions.HaarToSphere

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem lintegral_polar_sphereMeasure {n : ℕ} (hn : 1 ≤ n)
    {F : Space n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, F x) = ∫⁻ ω, ∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (n - 1)) * F (t • ω) ∂volume ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
  let : NeZero n := ⟨by omega⟩
  let E := Space n
  let H := homeomorphUnitSphereProd E
  have h1 : (∫⁻ x, F x) = ∫⁻ x : ({(0 : E)}ᶜ : Set E), F x ∂volume.comap Subtype.val := by
    rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
  have h2 : (∫⁻ x : ({(0 : E)}ᶜ : Set E), F x ∂volume.comap Subtype.val) =
      ∫⁻ z : sphere (0 : E) 1 × Ioi (0 : ℝ), F (z.2.1 • z.1.1)
        ∂(volume.toSphere.prod (Measure.volumeIoiPow (n - 1))) := by
    have h := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
      H.measurableEmbedding (fun z ↦ F (H.symm z))
    simpa only [H, Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe,
      E, Space, finrank_euclideanSpace, Fintype.card_fin] using h
  rw [h1, h2, lintegral_prod _ (by fun_prop)]
  have hinner (ω : sphere (0 : E) 1) :
      (∫⁻ t : Ioi (0 : ℝ), F (t.1 • ω.1) ∂Measure.volumeIoiPow (n - 1)) =
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (n - 1)) * F (t • ω.1) := by
    rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul]
    · exact lintegral_subtype_comap measurableSet_Ioi
        (fun t : ℝ ↦ ENNReal.ofReal (t ^ (n - 1)) * F (t • ω.1))
    · fun_prop
    · fun_prop
  simp_rw [hinner]
  rw [OAI.Analysis.Fourier.Restriction.sphereMeasure, lintegral_map]
  · fun_prop
  · exact measurable_subtype_coe

end OAI.Analysis.Fourier.Restriction
