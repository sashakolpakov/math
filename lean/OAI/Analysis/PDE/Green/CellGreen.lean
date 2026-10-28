import OAI.Analysis.PDE.Green.BoxGreen
import OAI.Analysis.PDE.Green.SecondGreen

/-! The periodic-cell divergence and Green identities in volume-preserving coordinates. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

theorem fderiv_comp_linear_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {f : F → ℝ} (hf : ContDiff ℝ 1 f) (x v : E) :
    fderiv ℝ (fun y => f (L y)) x v = fderiv ℝ f (L x) (L v) := by
  simpa [Function.comp_def] using congrArg (fun Q : E →L[ℝ] ℝ => Q v)
    (fderiv_comp x (hf.differentiable (by norm_num) (L x)) L.differentiableAt)

theorem integral_divergence_coordinate_cell_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] {m : ℕ}
    (e : E ≃L[ℝ] (Fin (m + 1) → ℝ)) (he : MeasurePreserving e)
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → E → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r : E → ℝ} (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ e ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (hzero : ∀ x, r x = 0 →
      ∑ i, fderiv ℝ r x (e.symm (Pi.single i 1)) * F i x = 0)
    (hface : ∀ i, ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      (r (e.symm (i.insertNth (b i) y)) = r (e.symm (i.insertNth (a i) y)) ∧
        F i (e.symm (i.insertNth (b i) y)) = F i (e.symm (i.insertNth (a i) y))) ∨
      (0 ≤ r (e.symm (i.insertNth (b i) y)) ∧ 0 ≤ r (e.symm (i.insertNth (a i) y))) ∨
      (F i (e.symm (i.insertNth (b i) y)) = 0 ∧ F i (e.symm (i.insertNth (a i) y)) = 0)) :
    (∫ x in (e ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∑ i, fderiv ℝ (F i) x (e.symm (Pi.single i 1))) = 0 := by
  have hc : ContDiff ℝ 2 (fun y => r (e.symm y)) := hr.comp e.symm.contDiff
  have hfc : ∀ i, ContDiff ℝ 1 (fun y => F i (e.symm y)) :=
    fun i => (hF i).comp e.symm.contDiff
  have hdr (y v : Fin (m + 1) → ℝ) :
      fderiv ℝ (fun z => r (e.symm z)) y v = fderiv ℝ r (e.symm y) (e.symm v) := by
    simpa only using! fderiv_comp_linear_apply e.symm.toContinuousLinearMap
      (hr.of_le (by norm_num)) y v
  have hdf (i) (y v : Fin (m + 1) → ℝ) :
      fderiv ℝ (fun z => F i (e.symm z)) y v =
        fderiv ℝ (F i) (e.symm y) (e.symm v) := by
    simpa only using! fderiv_comp_linear_apply e.symm.toContinuousLinearMap (hF i) y v
  have hreg : ∀ y ∈ Icc a b, r (e.symm y) = 0 →
      fderiv ℝ (fun z => r (e.symm z)) y ≠ 0 := by
    intro y hy hyr hz
    apply hrne (e.symm y) (by simpa using hy) hyr
    ext v
    have hh := congrArg (fun Q : (Fin (m + 1) → ℝ) →L[ℝ] ℝ => Q (e v)) hz
    simpa only [hdr, e.symm_apply_apply, zero_apply] using hh
  have htang : ∀ y, r (e.symm y) = 0 →
      ∑ i, fderiv ℝ (fun z => r (e.symm z)) y (Pi.single i 1) * F i (e.symm y) = 0 := by
    intro y hy
    simpa only [hdr] using hzero (e.symm y) hy
  have hz := integral_divergence_cell_sublevel_zero a b hab
    (fun i y => F i (e.symm y)) hfc hc hreg htang hface
  simp_rw [hdf] at hz
  have hm := he.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding
    (fun y => ∑ i, fderiv ℝ (F i) (e.symm y) (e.symm (Pi.single i 1)))
    (Icc a b ∩ {y | r (e.symm y) < 0})
  simpa only [Set.preimage_inter, Set.preimage_ofPred_eq, e.symm_apply_apply, hz] using hm

end OAI.Analysis.PDE.Green
