import OAI.Geometry.Nikodym.ProjectiveLp
import OAI.Geometry.Nikodym.CoordinateMeasure
import OAI.Geometry.Nikodym.StripMass

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Module
open scoped ENNReal
namespace OAI.Geometry.Nikodym

def stripBox (d : ℕ) (V : ℝ) : Set (Space d × ℝ) :=
  {p | (1/2 : ℝ) ≤ |p.2| ∧ |p.2| ≤ 3 ∧ ‖p.1‖ ≤ 2+2*V}

theorem measurableSet_stripBox (d : ℕ) (V : ℝ) : MeasurableSet (stripBox d V) := by
  unfold stripBox
  measurability

def stripInput (d : ℕ) (V : ℝ) (f : Space (d+1) → ℂ) : Space (d+1) → ℂ :=
  ((projectiveJoin d).symm ⁻¹' stripBox d V).indicator f

def stripPullback (d : ℕ) (V : ℝ) (f : Space (d+1) → ℂ) : Space (d+1) → ℂ :=
  projectivePullback (projectiveJoin d) (stripInput d V f)

theorem measurable_stripInput {d : ℕ} (V : ℝ) {f : Space (d+1) → ℂ} (hf : Measurable f) :
    Measurable (stripInput d V f) :=
  hf.indicator ((measurableSet_stripBox d V).preimage (projectiveJoin d).symm.continuous.measurable)

theorem measurable_stripPullback {d : ℕ} (V : ℝ) {f : Space (d+1) → ℂ} (hf : Measurable f) :
    Measurable (stripPullback d V f) :=
  measurable_projectivePullback _ (measurable_stripInput V hf)

theorem stripInput_join {d : ℕ} (V : ℝ) (f : Space (d+1) → ℂ) (p : Space d × ℝ) :
    stripInput d V f (projectiveJoin d p) = (stripBox d V).indicator
      (fun q => f (projectiveJoin d q)) p := by
  by_cases hp : p ∈ stripBox d V <;> simp [stripInput,hp]

theorem stripInput_on_neighborhood {d : ℕ} (V : ℝ) (f : Space (d+1) → ℂ)
    {x v : Space d} {δ : ℝ} (hx : ‖x‖ ≤ 1) (hv : ‖v‖ ≤ V) (hδ : δ ≤ 1/2)
    {p : Space d × ℝ} (hp : p ∈ neighborhood δ (linePiece x v 1 2)) :
    stripInput d V f (projectiveJoin d p) = f (projectiveJoin d p) := by
  rw [stripInput_join]
  apply indicator_of_mem
  have h := normalized_neighborhood_in_strip hx hv hδ p hp
  refine ⟨h.1,h.2.1,?_⟩
  convert h.2.2 using 1 ; ring

theorem stripPullback_join {d : ℕ} (V : ℝ) (f : Space (d+1) → ℂ) (p : Space d × ℝ) :
    stripPullback d V f (projectiveJoin d p) =
      (stripBox d V).indicator (fun q => f (projectiveJoin d q)) (projective p) := by
  simp only [stripPullback,projectivePullback,ContinuousLinearEquiv.symm_apply_apply,stripInput_join]

theorem eLpNorm_stripPullback {d : ℕ} {V : ℝ} (hV : 0 ≤ V)
    {f : Space (d+1) → ℂ} (hf : Measurable f) (p : ℝ≥0∞) :
    eLpNorm (stripPullback d V f) p volume ≤
      (ENNReal.ofReal (projectiveDistortion (1/2) (2+2*V)) ^ (d+1)) ^
        (1/p).toReal * eLpNorm f p volume := by
  let : (volume : Measure (Space d × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have h := eLpNorm_projective_truncated (volume : Measure (Space d × ℝ))
    (by norm_num : (0:ℝ)<1/2) (by positivity : 0 ≤ 2+2*V)
    (measurableSet_stripBox d V) (fun q hq => ⟨hq.1,hq.2.2⟩)
    (hf.comp (projectiveJoin d).continuous.measurable) p
  have hi : eLpNorm (fun q : Space d × ℝ => f (projectiveJoin d q)) p volume =
      eLpNorm f p volume := by
    exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (measurePreserving_projectiveJoin d)
  have ho : eLpNorm (fun q => (stripBox d V).indicator
      (fun y => f (projectiveJoin d y)) (projective q)) p volume =
      eLpNorm (stripPullback d V f) p volume := by
    have he : (fun q => (stripBox d V).indicator
        (fun y => f (projectiveJoin d y)) (projective q)) =
        stripPullback d V f ∘ projectiveJoin d := by
      funext q
      exact (stripPullback_join V f q).symm
    rw [he]
    exact eLpNorm_comp_measurePreserving (measurable_stripPullback V hf).aestronglyMeasurable
      (measurePreserving_projectiveJoin d)
  simp only [Function.comp_def] at h
  rw [ho,hi] at h
  simpa only [Module.finrank_prod,Space,finrank_euclideanSpace,Fintype.card_fin,
    Module.finrank_self] using! h

end OAI.Geometry.Nikodym
