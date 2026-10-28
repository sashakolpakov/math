import OAI.Analysis.Calculus.Current.SourceProperties

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Matrix Matrix.Norms.Elementwise Topology ContDiff ComplexOrder

/-- A real spatial displacement written in the null coordinates. -/
def nullSpatialShift {d : ℕ} (x : OAI.Analysis.Calculus.Current.SpatialSpace d) : OAI.Analysis.Calculus.Current.Index d → ℝ
  | none => -x none / Real.sqrt 2
  | some none => -x none / Real.sqrt 2
  | some (some i) => -x (some i)

theorem continuous_nullSpatialShift (d : ℕ) : Continuous (nullSpatialShift (d := d)) := by
  apply continuous_pi
  intro i
  cases i with
  | none => dsimp only [nullSpatialShift]; fun_prop
  | some i => cases i <;> dsimp only [nullSpatialShift] <;> fun_prop

def spatialCubeVector {d : ℕ} (t : OAI.Analysis.Calculus.Current.SpatialCube d) : OAI.Analysis.Calculus.Current.SpatialSpace d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin d) => ℝ)).symm (fun i => (t i : ℝ))

theorem continuous_spatialCubeVector (d : ℕ) : Continuous (spatialCubeVector (d := d)) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin d) => ℝ)).symm.continuous.comp
  exact continuous_pi (fun i => continuous_subtype_val.comp (continuous_apply i))

/-- Kernel periodization in the lattice `100 R ℤⁿ`, expressed on a fixed
compact cube. In a sector frame `R` is the physical orthogonal lattice map. -/
def latticeKernelMeasure {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h : ℝ) : Measure (OAI.Analysis.Calculus.Current.SpatialCube d) :=
  (OAI.Analysis.Calculus.Current.sourceKernelMeasure d h).map (fun x => OAI.Analysis.Calculus.Current.wrapSpatial d (R.symm x))

theorem latticeKernelMeasure_isProbability {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h : ℝ) (hh : 0 < h) :
    IsProbabilityMeasure (latticeKernelMeasure R h) := by
  let := OAI.Analysis.Calculus.Current.sourceKernelMeasure_isProbability d h hh
  exact (Measure.isProbabilityMeasure_map_iff
    ((OAI.Analysis.Calculus.Current.measurable_wrapSpatial d).comp R.symm.continuous.measurable).aemeasurable).mpr inferInstance

def latticeCubeShift {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (t : OAI.Analysis.Calculus.Current.SpatialCube d) : OAI.Analysis.Calculus.Current.Index d → ℝ :=
  nullSpatialShift (R (spatialCubeVector t))

theorem continuous_latticeCubeShift {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) :
    Continuous (latticeCubeShift R) :=
  (continuous_nullSpatialShift d).comp (R.continuous.comp (continuous_spatialCubeVector d))

theorem latticeCubeShift_time_zero {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (t : OAI.Analysis.Calculus.Current.SpatialCube d) : latticeCubeShift R t none - latticeCubeShift R t (some none) = 0 := by
  simp [latticeCubeShift, nullSpatialShift]

theorem latticeKernelMeasure_refl (d : ℕ) (h : ℝ) :
    latticeKernelMeasure (ContinuousLinearEquiv.refl ℝ (OAI.Analysis.Calculus.Current.SpatialSpace d)) h =
      OAI.Analysis.Calculus.Current.periodizedKernelMeasure d h := rfl

theorem latticeCubeShift_refl (d : ℕ) :
    latticeCubeShift (ContinuousLinearEquiv.refl ℝ (OAI.Analysis.Calculus.Current.SpatialSpace d)) = OAI.Analysis.Calculus.Current.cubeSpatialShift := by
  funext t i
  cases i with
  | none => rfl
  | some i => cases i <;> rfl

variable {d : ℕ} {ι : Type*} [Fintype ι]

local instance : ContinuousENorm (Matrix (OAI.Analysis.Calculus.Current.Index d) (OAI.Analysis.Calculus.Current.Index d) (Quaternion ℝ)) :=
  inferInstanceAs (ContinuousENorm (OAI.Analysis.Calculus.Current.Index d → OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ))

/-- The same source current on a lattice that is not assumed axis-aligned. -/
def latticeRegularizedCurrent (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) : Matrix (OAI.Analysis.Calculus.Current.Index d) (OAI.Analysis.Calculus.Current.Index d) (Quaternion ℝ) :=
  OAI.Analysis.Calculus.Current.regularizedCurrent (latticeKernelMeasure R h) (latticeCubeShift R) h a κ cR cI v x z

theorem latticeRegularizedCurrent_refl (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) :
    latticeRegularizedCurrent (ContinuousLinearEquiv.refl ℝ (OAI.Analysis.Calculus.Current.SpatialSpace d)) h a κ cR cI v x z =
      OAI.Analysis.Calculus.Current.sourceRegularizedCurrent h a κ cR cI v x z := by
  simp only [latticeRegularizedCurrent, latticeKernelMeasure_refl, latticeCubeShift_refl,
    OAI.Analysis.Calculus.Current.sourceRegularizedCurrent]

theorem integrable_latticeWave_translates (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h : ℝ) (hh : 0 < h) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hY : z none ≠ 0) :
    Integrable (fun t => OAI.Analysis.Calculus.Current.waveCurrent κ cR cI v (x + latticeCubeShift R t) z)
      (latticeKernelMeasure R h) := by
  let := latticeKernelMeasure_isProbability R h hh
  exact OAI.Analysis.Calculus.Current.integrable_waveCurrent_translate _ _ (continuous_latticeCubeShift R) κ cR cI v x z hY

theorem latticeRegularizedCurrent_contDiffAt (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (hh : 0 < h) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (q : OAI.Analysis.Calculus.Current.CurrentSpace d) (hq : q ∈ OAI.Analysis.Calculus.Current.currentNonzeroDomain d) :
    ContDiffAt ℝ ∞ (fun y : OAI.Analysis.Calculus.Current.CurrentSpace d => latticeRegularizedCurrent R h a κ cR cI v y.1 y.2) q := by
  let := latticeKernelMeasure_isProbability R h hh
  exact OAI.Analysis.Calculus.Current.contDiffAt_regularizedCurrent _ _ (continuous_latticeCubeShift R) h a κ cR cI v q hq

theorem latticeRegularizedCurrent_divergence_zero (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (hh : 0 < h) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (q : OAI.Analysis.Calculus.Current.CurrentSpace d) (hq : q ∈ OAI.Analysis.Calculus.Current.currentNonzeroDomain d) (b : OAI.Analysis.Calculus.Current.Index d) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots (fun p => fderiv ℝ
      (fun y : OAI.Analysis.Calculus.Current.CurrentSpace d => latticeRegularizedCurrent R h a κ cR cI v y.1 y.2) q
      (OAI.Analysis.Calculus.Current.currentDirection p)) b = 0 := by
  let := latticeKernelMeasure_isProbability R h hh
  exact OAI.Analysis.Calculus.Current.regularizedCurrent_divergence_zero _ _ (continuous_latticeCubeShift R) h a κ cR cI v q hq b

theorem latticeRegularizedCurrent_isHermitian (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (hh : 0 < h) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hY : z none ≠ 0) :
    (latticeRegularizedCurrent R h a κ cR cI v x z).IsHermitian :=
  OAI.Analysis.Calculus.Current.regularizedCurrent_isHermitian _ _ h a κ cR cI v x z
    (integrable_latticeWave_translates R h hh κ cR cI v x z hY)

theorem latticeRegularizedCurrent_posSemidef (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (hh : 0 < h) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hY : z none ≠ 0) :
    (OAI.LinearAlgebra.Moore.complexify (latticeRegularizedCurrent R h a κ cR cI v x z)).PosSemidef :=
  OAI.Analysis.Calculus.Current.regularizedCurrent_posSemidef _ _ h a κ cR cI v x z hh.le hY
    (integrable_latticeWave_translates R h hh κ cR cI v x z hY)

theorem latticeRegularizedCurrent_time_pos (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (hh : 0 < h) (ha : a ≠ 0) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hY : z none ≠ 0)
    (hr : OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a z ≤ 0) :
    0 < OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h a κ cR cI v x z) :=
  OAI.Analysis.Calculus.Current.regularizedCurrent_time_pos _ _ h a κ cR cI v x z hh ha hY hr
    (integrable_latticeWave_translates R h hh κ cR cI v x z hY)

theorem latticeRegularizedCurrent_background_mul (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a : ℝ) (hh : 0 < h) (ha : a ≠ 0) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hY : z none ≠ 0) :
    OAI.Analysis.Calculus.Current.backgroundHessian z * latticeRegularizedCurrent R h a κ cR cI v x z = 0 :=
  OAI.Analysis.Calculus.Current.regularizedCurrent_background_mul _ _ h a κ cR cI v x z ha hY
    (integrable_latticeWave_translates R h hh κ cR cI v x z hY)

end OAI.Analysis.PDE.Concentration
