import OAI.Analysis.PDE.Green.WeightedFlux
import OAI.Analysis.PDE.Green.CellGreen

/-! Weighted small-flux estimates in volume-preserving coordinates. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory

theorem coordinate_weighted_small_divergence_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] {m : ℕ}
    (e : E ≃L[ℝ] (Fin (m + 1) → ℝ)) (he : MeasurePreserving e)
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → E → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r q₀ q₁ v : E → ℝ} (hr : ContDiff ℝ 2 r)
    (hq₀ : ContDiff ℝ 1 q₀) (hq₁ : ContDiff ℝ 1 q₁) (hv : Continuous v)
    (hrne : ∀ x ∈ e ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    {ε W : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ k : ℕ, (∫ x in e ⁻¹' Icc a b, normalCutoffWeight (r x) k * ‖v x‖) ≤ W)
    (hzero : ∀ x, r x = 0 → q₁ x = 0)
    (hbound : ∀ x, r x = 0 → ‖q₀ x‖ ≤ ε)
    (hdecomp : ∀ x, (∑ i, fderiv ℝ r x (e.symm (Pi.single i 1)) * F i x) =
      v x * q₀ x + q₁ x)
    (hface : CompatibleBoxFaces a b (fun y => r (e.symm y)) (fun i y => F i (e.symm y))) :
    ‖∫ x in (e ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∑ i, fderiv ℝ (F i) x (e.symm (Pi.single i 1))‖ ≤ ε * W := by
  have hc : ContDiff ℝ 2 (fun y => r (e.symm y)) := hr.comp e.symm.contDiff
  have hfc : ∀ i, ContDiff ℝ 1 (fun y => F i (e.symm y)) :=
    fun i => (hF i).comp e.symm.contDiff
  have hdr (y w : Fin (m + 1) → ℝ) :
      fderiv ℝ (fun z => r (e.symm z)) y w = fderiv ℝ r (e.symm y) (e.symm w) := by
    simpa only using! fderiv_comp_linear_apply e.symm.toContinuousLinearMap
      (hr.of_le (by norm_num)) y w
  have hdf (i) (y w : Fin (m + 1) → ℝ) :
      fderiv ℝ (fun z => F i (e.symm z)) y w =
        fderiv ℝ (F i) (e.symm y) (e.symm w) := by
    simpa only using! fderiv_comp_linear_apply e.symm.toContinuousLinearMap (hF i) y w
  have hreg : ∀ y ∈ Icc a b, r (e.symm y) = 0 →
      fderiv ℝ (fun z => r (e.symm z)) y ≠ 0 := by
    intro y hy hyr hz
    apply hrne (e.symm y) (by simpa using hy) hyr
    ext w
    have hh := congrArg (fun Q : (Fin (m + 1) → ℝ) →L[ℝ] ℝ => Q (e w)) hz
    simpa only [hdr, e.symm_apply_apply, zero_apply] using hh
  have hweight (k : ℕ) : (∫ y in Icc a b,
      normalCutoffWeight (r (e.symm y)) k * ‖v (e.symm y)‖) ≤ W := by
    have hm := he.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding
      (fun y => normalCutoffWeight (r (e.symm y)) k * ‖v (e.symm y)‖) (Icc a b)
    rw [← hm]
    simpa only [e.symm_apply_apply] using hW k
  have hdec (y : Fin (m + 1) → ℝ) :
      (∑ i, fderiv ℝ (fun z => r (e.symm z)) y (Pi.single i 1) * F i (e.symm y)) =
        v (e.symm y) * q₀ (e.symm y) + q₁ (e.symm y) := by
    simpa only [hdr] using hdecomp (e.symm y)
  have hz := weighted_small_normal_divergence_bound a b hab (fun i y => F i (e.symm y))
    hfc hc (hq₀.comp e.symm.contDiff) (hq₁.comp e.symm.contDiff) (hv.comp e.symm.continuous)
    hreg hε hweight (fun y => hzero (e.symm y)) (fun y => hbound (e.symm y)) hdec hface
  simp_rw [hdf] at hz
  have hm := he.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding
    (fun y => ∑ i, fderiv ℝ (F i) (e.symm y) (e.symm (Pi.single i 1)))
    (Icc a b ∩ {y | r (e.symm y) < 0})
  have hEq : (∫ x in (e ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∑ i, fderiv ℝ (F i) x (e.symm (Pi.single i 1))) =
      ∫ y in Icc a b ∩ {y | r (e.symm y) < 0},
        ∑ i, fderiv ℝ (F i) (e.symm y) (e.symm (Pi.single i 1)) := by
    simpa only [Set.preimage_inter, Set.preimage_ofPred_eq, e.symm_apply_apply] using hm
  rw [hEq]
  exact hz

end OAI.Analysis.PDE.Green
