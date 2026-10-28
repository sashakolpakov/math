import OAI.Geometry.Nikodym.ScaledStripLp
import OAI.Geometry.Nikodym.DilationIntegral
import OAI.Geometry.Nikodym.DyadicTube

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym

def scaledStripRegion {d : ℕ} (δ r : ℝ) (x : Space (d+1)) (v : Space d) : Set (Space (d+1)) :=
  {y | r⁻¹ • (projectiveJoin d).symm (y-x) ∈ neighborhood (δ/|r|) (linePiece 0 v 1 2)}

theorem isOpen_scaledStripRegion {d : ℕ} (δ r : ℝ) (x : Space (d+1)) (v : Space d) :
    IsOpen (scaledStripRegion δ r x v) :=
  (isOpen_neighborhood _ _).preimage (by fun_prop)

theorem scaledStripRegion_preimage {d : ℕ} (δ : ℝ) {r : ℝ} (hr : r ≠ 0)
    (x : Space (d+1)) (v : Space d) :
    (fun y : Space (d+1) => r • y) ⁻¹' scaledStripRegion δ r x v =
      physicalStrip (δ/|r|) v (r⁻¹ • x) := by
  ext y
  simp only [mem_preimage,scaledStripRegion,physicalStrip,Set.mem_ofPred_eq]
  simp [map_sub,map_smul,smul_sub,smul_smul,hr]

theorem normalized_scaled_mass_coefficient (d : ℕ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ENNReal.ofReal (R^(d+1))*ENNReal.ofReal ((δ/R)^d) =
      ENNReal.ofReal R*ENNReal.ofReal (δ^d) := by
  rw [← ENNReal.ofReal_mul (pow_nonneg hR.le _),← ENNReal.ofReal_mul hR.le]
  congr 1
  rw [div_pow,pow_succ]
  field_simp

theorem scaledStripRegion_average_le {d : ℕ} {δ r V : ℝ} (hδ : 0 < δ) (hr : r ≠ 0)
    {v : Space d} (hv : ‖v‖ ≤ V) {f : Space (d+1) → ℂ} (hf : Measurable f)
    (x : Space (d+1)) :
    (∫⁻ y in scaledStripRegion δ r x v, ‖f y‖ₑ) / ENNReal.ofReal (δ^d) ≤
      scaledStrip δ V r f x := by
  have hrp := abs_pos.mpr hr
  have hη : 0 < δ/|r| := div_pos hδ hrp
  have hm : (∫⁻ y in physicalStrip (δ/|r|) v (r⁻¹ • x), ‖f (r • y)‖ₑ) ≤
      fullStrip (δ/|r|) V (fun y => f (r • y)) (r⁻¹ • x) * ENNReal.ofReal ((δ/|r|)^d) := by
    apply (ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hη d)))
      ENNReal.ofReal_ne_top).mp
    exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)
  rw [setLIntegral_dilate hr (isOpen_scaledStripRegion δ r x v).measurableSet hf.enorm,
    scaledStripRegion_preimage δ hr x v]
  apply (ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hδ d)))
    ENNReal.ofReal_ne_top).mpr
  apply (mul_le_mul' le_rfl hm).trans_eq
  unfold scaledStrip
  calc
    _ = (ENNReal.ofReal (|r|^(d+1))*ENNReal.ofReal ((δ/|r|)^d)) *
        fullStrip (δ/|r|) V (fun y => f (r • y)) (r⁻¹ • x) := by ac_rfl
    _ = _ := by rw [normalized_scaled_mass_coefficient d hrp hδ]; ac_rfl

theorem linePiece_average_le_scaledStrip {d : ℕ} {δ r V : ℝ} (hδ : 0 < δ) (hr : r ≠ 0)
    {v : Space d} (hv : ‖v‖ ≤ V) {f : Space (d+1) → ℂ} (hf : Measurable f)
    (x : Space (d+1)) :
    (∫⁻ y in neighborhood δ (scaledLinePiece x v r), ‖f y‖ₑ) / ENNReal.ofReal (δ^d) ≤
      scaledStrip δ V r f x := by
  apply (ENNReal.div_le_div_right ?_ _).trans (scaledStripRegion_average_le hδ hr hv hf x)
  exact lintegral_mono_set fun y hy => normalize_scaledLinePiece_neighborhood hr x v hy

end OAI.Geometry.Nikodym
