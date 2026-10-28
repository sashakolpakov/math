import OAI.Analysis.Calculus.Current.Periodization

/-! Structural properties of the source's concrete regularized current. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Matrix Matrix.Norms.Elementwise Topology ComplexOrder
variable {d : ℕ} {ι : Type*} [Fintype ι]

local instance : ContinuousENorm (Matrix (Index d) (Index d) (Quaternion ℝ)) :=
  inferInstanceAs (ContinuousENorm (Index d → Index d → Quaternion ℝ))

theorem integrable_sourceWave_translates (h : ℝ) (hh : 0 < h)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) : Integrable
      (fun t => waveCurrent κ cR cI v (x + cubeSpatialShift t) z) (periodizedKernelMeasure d h) := by
  let := periodizedKernelMeasure_isProbability d h hh
  exact integrable_waveCurrent_translate _ _ (continuous_cubeSpatialShift d) κ cR cI v x z hY

theorem sourceRegularizedCurrent_isHermitian (h a : ℝ) (hh : 0 < h)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) : (sourceRegularizedCurrent h a κ cR cI v x z).IsHermitian :=
  regularizedCurrent_isHermitian _ _ h a κ cR cI v x z
    (integrable_sourceWave_translates h hh κ cR cI v x z hY)

theorem sourceRegularizedCurrent_posSemidef (h a : ℝ) (hh : 0 < h)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) : (OAI.LinearAlgebra.Moore.complexify (sourceRegularizedCurrent h a κ cR cI v x z)).PosSemidef :=
  regularizedCurrent_posSemidef _ _ h a κ cR cI v x z hh.le hY
    (integrable_sourceWave_translates h hh κ cR cI v x z hY)

theorem sourceRegularizedCurrent_time_pos (h a : ℝ) (hh : 0 < h) (ha : a ≠ 0)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (hr : fiberDefining (1 / 10) a z ≤ 0) :
    0 < timeComponent (sourceRegularizedCurrent h a κ cR cI v x z) :=
  regularizedCurrent_time_pos _ _ h a κ cR cI v x z hh ha hY hr
    (integrable_sourceWave_translates h hh κ cR cI v x z hY)

theorem sourceRegularizedCurrent_tangent (h a : ℝ) (hh : 0 < h) (ha : a ≠ 0)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (ξ : Index d → OAI.Analysis.Calculus.Quaternion.Q) :
    (∑ b, complexK (phaseRow (ratio z) b) *
      (sourceRegularizedCurrent h a κ cR cI v x z *ᵥ ξ) b) = 0 :=
  regularizedCurrent_tangent _ _ h a κ cR cI v x z ha hY
    (integrable_sourceWave_translates h hh κ cR cI v x z hY) ξ

theorem sourceRegularizedCurrent_background_pairing (h a : ℝ) (hh : 0 < h) (ha : a ≠ 0)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) :
    (backgroundHessian z * sourceRegularizedCurrent h a κ cR cI v x z).trace.re = 0 :=
  regularizedCurrent_background_pairing _ _ h a κ cR cI v x z ha hY
    (integrable_sourceWave_translates h hh κ cR cI v x z hY)

end OAI.Analysis.Calculus.Current
