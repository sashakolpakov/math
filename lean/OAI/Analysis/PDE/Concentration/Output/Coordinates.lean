import OAI.Analysis.PDE.Concentration.Packet.Coordinates

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

def physicalNullTime (d : ℕ) (t : ℝ) : OAI.Analysis.Calculus.Current.Index d → ℝ
  | none => t / Real.sqrt 2
  | some none => -t / Real.sqrt 2
  | some (some _) => 0

private theorem fin_cases_one_output {d : ℕ} {α : Sort*} (a : α) (f : Fin (d + 1) → α) :
    Fin.cases a f (1 : Fin (d + 2)) = f 0 := rfl

/-- The actual time-dependent packet coordinate, without restricting the
physical time to the input slice. -/
theorem physicalToNullCurrentPoint_output_real (d : ℕ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    (physicalToNullCurrentPoint d (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y)).1 =
      physicalNullTime d (z (0, 0)) - nullSpatialShift (physicalSpatialRealVector d y) := by
  funext i
  change (nullCoordinateProjection d
    (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift (nullRotation d)) (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y))).1 i = _
  rw [nullCoordinateProjection_real]
  cases i with
  | none =>
    simp [nullIndexEquiv_symm_none, nullRotation_action_time, physicalSpatialRealVector,
      nullSpatialShift, physicalNullTime, OAI.Analysis.PDE.Green.fiberEmbedding, OAI.Analysis.PDE.Green.timeInjection, OAI.Analysis.PDE.Green.spatialInjection,
      OAI.Analysis.PDE.Green.spatialInjectionLinear, fin_cases_one_output]
    ring
  | some i =>
    cases i with
    | none =>
      simp [nullIndexEquiv_symm_some_none, nullRotation_action_longitudinal, physicalSpatialRealVector,
        nullSpatialShift, physicalNullTime, OAI.Analysis.PDE.Green.fiberEmbedding, OAI.Analysis.PDE.Green.timeInjection, OAI.Analysis.PDE.Green.spatialInjection,
        OAI.Analysis.PDE.Green.spatialInjectionLinear, fin_cases_one_output]
      ring
    | some i =>
      simp [nullIndexEquiv_symm_some_some, nullRotation_action_transverse, physicalSpatialRealVector,
        nullSpatialShift, physicalNullTime, OAI.Analysis.PDE.Green.fiberEmbedding, OAI.Analysis.PDE.Green.timeInjection, OAI.Analysis.PDE.Green.spatialInjection,
        OAI.Analysis.PDE.Green.spatialInjectionLinear]

theorem physicalLatticeCurrent_output_density {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z y) 0 0).re =
      OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h a κ cR cI v
        (physicalNullTime d (z (0, 0)) - nullSpatialShift (physicalSpatialRealVector d y))
        (OAI.Analysis.Calculus.Current.physicalEmbedding (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.physicalSpatialProjection d y))) := by
  rw [physicalLatticeCurrent_time_entry, physicalToNullCurrentPoint_output_real,
    physicalToNullCurrentPoint_fiber_imaginary]

theorem physicalSpatialRealVector_sub (d : ℕ) (x y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    physicalSpatialRealVector d (x - y) =
      physicalSpatialRealVector d x - physicalSpatialRealVector d y := by
  ext i
  rfl

theorem physicalSpatialRealVector_norm_le (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    ‖physicalSpatialRealVector d x‖ ≤ ‖x‖ := by
  have hs : ‖physicalSpatialRealVector d x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change (∑ i, ‖x ((finSuccEquiv d).symm i, 0)‖ ^ 2) ≤ ∑ i, ‖x i‖ ^ 2
    rw [(finSuccEquiv d).symm.sum_comp (fun i => ‖x (i, 0)‖ ^ 2), Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖x (i, j)‖) (Finset.mem_univ (0 : Fin 3))
  nlinarith [norm_nonneg (physicalSpatialRealVector d x), norm_nonneg x]

theorem physicalSpatialRealVector_distance (d : ℕ) (x y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :
    ‖physicalSpatialRealVector d x - physicalSpatialRealVector d y‖ ≤ ‖x - y‖ := by
  rw [← physicalSpatialRealVector_sub]
  exact physicalSpatialRealVector_norm_le d (x - y)

end OAI.Analysis.PDE.Concentration
