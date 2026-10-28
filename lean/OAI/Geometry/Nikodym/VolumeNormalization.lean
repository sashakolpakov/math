import OAI.Geometry.Nikodym.Majorant
import OAI.MeasureTheory.Kakeya.Volume
import OAI.Geometry.Nikodym.Measurability

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym


theorem normalize_mass_of_lower {c q : ℝ} (hc : 0 < c) (_ : 0 < q)
    {v : ℝ≥0∞} (hv : ENNReal.ofReal (c*q) ≤ v) (m : ℝ≥0∞) :
    m/v ≤ ENNReal.ofReal c⁻¹ * (m/ENNReal.ofReal q) := by
  calc
    m/v ≤ m/ENNReal.ofReal (c*q) := by gcongr
    _ = _ := by
      rw [ENNReal.ofReal_mul hc.le,div_eq_mul_inv,ENNReal.mul_inv,
        ENNReal.ofReal_inv_of_pos hc,div_eq_mul_inv]
      ac_rfl
      all_goals simp

theorem exists_nikodymMajorant_bound {d : ℕ} :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ N : ℕ,
      ∀ f : Space (d+1) → ℂ, Measurable f → ∀ x,
        nikodymMaximal δ f x ≤ ENNReal.ofReal c*tubeMajorant δ N f x := by
  obtain ⟨c,hc,hvol⟩ := OAI.MeasureTheory.Kakeya.exists_volume_tube_real_lower (n:=d+1) (by omega)
  refine ⟨c⁻¹,inv_pos.mpr hc,?_⟩
  intro δ hδ hδ1
  obtain ⟨N,hN⟩ := exists_tubeMajorant_mass_bound (d:=d) hδ
  refine ⟨N,?_⟩
  intro f hf x
  unfold nikodymMaximal
  refine iSup_le fun ω => iSup_le fun hω => iSup_le fun t => iSup_le fun ht => ?_
  have hx : x ∈ OAI.MeasureTheory.Kakeya.unitSegment ω (x-t•ω) := by
    refine ⟨t,ht,?_⟩
    abel
  have hv : ENNReal.ofReal (c*δ^d) ≤ volume (OAI.MeasureTheory.Kakeya.tube δ ω (x-t•ω)) := by
    apply (ENNReal.ofReal_le_ofReal (by simpa using hvol δ ω (x-t•ω) hδ hδ1 hω)).trans
    exact ENNReal.ofReal_toReal_le
  apply (normalize_mass_of_lower hc (pow_pos hδ d) hv _).trans
  exact mul_le_mul' le_rfl (hN f hf ω (x-t•ω) x hω hx)

end OAI.Geometry.Nikodym
