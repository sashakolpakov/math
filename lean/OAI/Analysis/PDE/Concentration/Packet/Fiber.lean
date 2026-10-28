import OAI.Analysis.PDE.Concentration.Physical.LatticeCurrent
import OAI.Analysis.PDE.Concentration.SpatialSplit
import OAI.Analysis.PDE.Concentration.RegularizedDensity

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

private theorem fin_cases_one {d : ℕ} {α : Sort*} (a : α) (f : Fin (d + 1) → α) :
    Fin.cases a f (1 : Fin (d + 2)) = f 0 := by
  change Fin.cases a f (0 : Fin (d + 1)).succ = f 0
  rfl

def physicalSpatialRealVector (d : ℕ) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) : OAI.Analysis.Calculus.Current.SpatialSpace d :=
  WithLp.toLp 2 (fun i => y ((finSuccEquiv d).symm i, 0))

theorem physicalToNullCurrentPoint_input_real (d : ℕ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hz : z (0, 0) = 0) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    (physicalToNullCurrentPoint d (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y)).1 =
      (0 : OAI.Analysis.Calculus.Current.Index d → ℝ) - nullSpatialShift (physicalSpatialRealVector d y) := by
  funext i
  change (nullCoordinateProjection d
    (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift (nullRotation d)) (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y))).1 i = _
  rw [nullCoordinateProjection_real]
  cases i with
  | none =>
    simp [nullIndexEquiv_symm_none, nullRotation_action_time, physicalSpatialRealVector,
      nullSpatialShift, OAI.Analysis.PDE.Green.fiberEmbedding, OAI.Analysis.PDE.Green.timeInjection, OAI.Analysis.PDE.Green.spatialInjection, OAI.Analysis.PDE.Green.spatialInjectionLinear, hz,
      fin_cases_one, neg_div]
  | some i =>
    cases i with
    | none =>
      simp [nullIndexEquiv_symm_some_none, nullRotation_action_longitudinal, physicalSpatialRealVector,
        nullSpatialShift, OAI.Analysis.PDE.Green.fiberEmbedding, OAI.Analysis.PDE.Green.timeInjection, OAI.Analysis.PDE.Green.spatialInjection, OAI.Analysis.PDE.Green.spatialInjectionLinear, hz,
        fin_cases_one, neg_div]
    | some i =>
      simp [nullIndexEquiv_symm_some_some, nullRotation_action_transverse, physicalSpatialRealVector,
        nullSpatialShift, OAI.Analysis.PDE.Green.fiberEmbedding, OAI.Analysis.PDE.Green.timeInjection, OAI.Analysis.PDE.Green.spatialInjection, OAI.Analysis.PDE.Green.spatialInjectionLinear]

theorem physicalToNullCurrentPoint_fiber_imaginary (d : ℕ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    (physicalToNullCurrentPoint d (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y)).2 =
      OAI.Analysis.Calculus.Current.physicalEmbedding (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.physicalSpatialProjection d y) := by
  rw [physicalToNullCurrentPoint_imaginary, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber]

/-- Exact identification of the PDE density on the real-time-zero physical
fiber with the packet density used in the Gaussian multiplier estimates. -/
theorem physicalLatticeCurrent_input_density {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hz : z (0, 0) = 0) (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) 0 0).re =
      OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h a κ cR cI v
        (0 - nullSpatialShift (physicalSpatialRealVector d y))
        (OAI.Analysis.Calculus.Current.physicalEmbedding (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.physicalSpatialProjection d y))) := by
  rw [physicalLatticeCurrent_time_entry, physicalToNullCurrentPoint_input_real d z hz,
    physicalToNullCurrentPoint_fiber_imaginary]

end OAI.Analysis.PDE.Concentration
