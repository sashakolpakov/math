import OAI.Geometry.Nikodym.StripMeasurability
import Mathlib.MeasureTheory.Group.LIntegral

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym


theorem linePiece_translation {d : ℕ} (x v : Space d) :
    linePiece x v 1 2 = (fun p : Space d × ℝ => p+(x,0)) '' linePiece 0 v 1 2 := by
  ext p
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact ⟨(t • v,t),⟨t,ht,by simp⟩,by simp [add_comm]⟩
  · rintro ⟨q,⟨t,ht,rfl⟩,rfl⟩
    exact ⟨t,ht,by simp [add_comm]⟩

theorem neighborhood_translation {E : Type*} [SeminormedAddCommGroup E]
    (δ : ℝ) (a p : E) (A : Set E) :
    p ∈ neighborhood δ ((fun q => q+a) '' A) ↔ p-a ∈ neighborhood δ A := by
  constructor
  · rintro ⟨q,⟨q0,hq0,rfl⟩,hd⟩
    exact ⟨q0,hq0,by simpa only [dist_eq_norm,sub_add_eq_sub_sub,sub_right_comm] using hd⟩
  · rintro ⟨q,hq,hd⟩
    exact ⟨q+a,⟨q,hq,rfl⟩,by simpa only [dist_eq_norm,sub_add_eq_sub_sub,sub_right_comm] using hd⟩

theorem mem_lineNeighborhood_translate {d : ℕ} (δ : ℝ) (x v : Space d)
    (p : Space d × ℝ) :
    p ∈ neighborhood δ (linePiece x v 1 2) ↔
      p-(x,0) ∈ neighborhood δ (linePiece 0 v 1 2) := by
  rw [linePiece_translation,neighborhood_translation]

def physicalStrip {d : ℕ} (δ : ℝ) (v : Space d) (z : Space (d+1)) : Set (Space (d+1)) :=
  {y | (projectiveJoin d).symm (y-z) ∈ neighborhood δ (linePiece 0 v 1 2)}

def fullStrip {d : ℕ} (δ V : ℝ) (f : Space (d+1) → ℂ) (z : Space (d+1)) : ℝ≥0∞ :=
  ⨆ v : Space d, ⨆ (_ : ‖v‖ ≤ V),
    (∫⁻ y in physicalStrip δ v z, ‖f y‖ₑ) / ENNReal.ofReal (δ^d)

theorem isOpen_physicalStrip {d : ℕ} (δ : ℝ) (v : Space d) (z : Space (d+1)) :
    IsOpen (physicalStrip δ v z) :=
  (isOpen_neighborhood _ _).preimage (by fun_prop)

theorem measurable_fullStrip {d : ℕ} (δ V : ℝ) {f : Space (d+1) → ℂ}
    (hf : Measurable f) : Measurable (fullStrip δ V f) := by
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_iSup
  intro v
  apply lowerSemicontinuous_iSup
  intro hv
  let F : Space (d+1) → Space (d+1) → ℝ≥0∞ := fun z =>
    (physicalStrip δ v z).indicator (fun y => ‖f y‖ₑ*(ENNReal.ofReal (δ^d))⁻¹)
  have hm (z) : AEMeasurable (F z) volume :=
    ((hf.enorm.mul_const _).indicator (isOpen_physicalStrip δ v z).measurableSet).aemeasurable
  have hl (y) : LowerSemicontinuous (fun z => F z y) := by
    change LowerSemicontinuous ({z | y ∈ physicalStrip δ v z}.indicator
      (fun _ => ‖f y‖ₑ*(ENNReal.ofReal (δ^d))⁻¹))
    have ho : IsOpen {z | y ∈ physicalStrip δ v z} :=
      (isOpen_neighborhood _ _).preimage (by fun_prop)
    exact ho.lowerSemicontinuous_indicator bot_le
  convert OAI.MeasureTheory.Kakeya.lowerSemicontinuous_lintegral_family F hm hl using 1
  funext z
  rw [lintegral_indicator (isOpen_physicalStrip δ v z).measurableSet,
    lintegral_mul_const _ hf.enorm]
  rfl

theorem fullStrip_eq_local {d : ℕ} (δ V : ℝ) {f : Space (d+1) → ℂ}
    (hf : Measurable f) (z : Space (d+1)) (x : Space d) :
    fullStrip δ V f (z+projectiveJoin d (x,0)) =
      stripMaximal δ V (fun y => f (z+y)) x := by
  unfold fullStrip stripMaximal
  congr 1
  funext v
  congr 1
  funext hv
  congr 1
  have hpres := (measurePreserving_add_left (volume : Measure (Space (d+1))) z).comp
    (measurePreserving_projectiveJoin d)
  have h := hpres.setLIntegral_comp_preimage
    (isOpen_physicalStrip δ v (z+projectiveJoin d (x,0))).measurableSet hf.enorm
  have hset : (fun p => z+projectiveJoin d p) ⁻¹'
      physicalStrip δ v (z+projectiveJoin d (x,0)) = neighborhood δ (linePiece x v 1 2) := by
    ext p
    simp only [mem_preimage,physicalStrip,Set.mem_ofPred_eq,add_sub_add_left_eq_sub,
      ← map_sub,ContinuousLinearEquiv.symm_apply_apply]
    exact (mem_lineNeighborhood_translate δ x v p).symm
  simp only [Function.comp_def] at h
  rw [hset] at h
  exact h.symm

end OAI.Geometry.Nikodym
