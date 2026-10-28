import OAI.Analysis.Calculus.Current.Kernel

/-! Periodization of the source kernel on the fixed spatial torus of side 100.
The compact cube represents the torus measure; no pointwise summation of a
periodized density is needed for averaging smooth periodic fields. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise Topology ContDiff

abbrev SpatialCube (d : ℕ) := Option (Fin d) → Set.Icc (0 : ℝ) 100

def wrapSpatial (d : ℕ) (x : SpatialSpace d) : SpatialCube d := fun i =>
  ⟨100 * Int.fract (x i / 100), by
    constructor
    · positivity
    · have hi := Int.fract_lt_one (x i / 100)
      linarith⟩

theorem measurable_wrapSpatial (d : ℕ) : Measurable (wrapSpatial d) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.subtype_mk
  have hi : Measurable (fun x : SpatialSpace d => x i / 100) := by fun_prop
  exact hi.fract.const_mul 100

/-- Pushforward under the quotient representative is periodization of a measure. -/
def periodizedKernelMeasure (d : ℕ) (h : ℝ) : Measure (SpatialCube d) :=
  (sourceKernelMeasure d h).map (wrapSpatial d)

theorem periodizedKernelMeasure_isProbability (d : ℕ) (h : ℝ) (hh : 0 < h) :
    IsProbabilityMeasure (periodizedKernelMeasure d h) := by
  let := sourceKernelMeasure_isProbability d h hh
  exact (Measure.isProbabilityMeasure_map_iff (measurable_wrapSpatial d).aemeasurable).mpr
    inferInstance

/-- Spatial translations in the null frame: the physical time coordinate is unchanged. -/
def cubeSpatialShift {d : ℕ} (x : SpatialCube d) : Index d → ℝ
  | none => -(x none : ℝ) / Real.sqrt 2
  | some none => -(x none : ℝ) / Real.sqrt 2
  | some (some i) => -(x (some i) : ℝ)

theorem continuous_cubeSpatialShift (d : ℕ) : Continuous (cubeSpatialShift (d := d)) := by
  apply continuous_pi
  intro i
  cases i with
  | none => exact ((continuous_subtype_val.comp (continuous_apply none)).neg).div_const _
  | some i =>
    cases i with
    | none => exact ((continuous_subtype_val.comp (continuous_apply none)).neg).div_const _
    | some i => exact (continuous_subtype_val.comp (continuous_apply (some i))).neg

theorem cubeSpatialShift_time_zero {d : ℕ} (x : SpatialCube d) :
    cubeSpatialShift x none - cubeSpatialShift x (some none) = 0 := by
  simp [cubeSpatialShift]

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- The exact cutoff-plus-cofactor regularization with the normalized periodized kernel. -/
def sourceRegularizedCurrent (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) : Matrix (Index d) (Index d) OAI.Analysis.Calculus.Quaternion.Q :=
  regularizedCurrent (periodizedKernelMeasure d h) cubeSpatialShift h a κ cR cI v x z

theorem sourceRegularizedCurrent_contDiffAt (h a : ℝ) (hh : 0 < h)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (q : CurrentSpace d)
    (hq : q ∈ currentNonzeroDomain d) :
    ContDiffAt ℝ ∞ (fun y : CurrentSpace d => sourceRegularizedCurrent h a κ cR cI v y.1 y.2) q := by
  let := periodizedKernelMeasure_isProbability d h hh
  exact contDiffAt_regularizedCurrent _ _ (continuous_cubeSpatialShift d) h a κ cR cI v q hq

theorem sourceRegularizedCurrent_divergence_zero (h a : ℝ) (hh : 0 < h)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (q : CurrentSpace d)
    (hq : q ∈ currentNonzeroDomain d) (b : Index d) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots (fun p => fderiv ℝ
      (fun y : CurrentSpace d => sourceRegularizedCurrent h a κ cR cI v y.1 y.2) q
      (currentDirection p)) b = 0 := by
  let := periodizedKernelMeasure_isProbability d h hh
  exact regularizedCurrent_divergence_zero _ _ (continuous_cubeSpatialShift d) h a κ cR cI v q hq b

end OAI.Analysis.Calculus.Current
