import OAI.Analysis.PDE.Concentration.SpatialL2

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current _root_.MeasureTheory Set

def spatialUnitCell (d : ℕ) : Set (OAI.Analysis.Calculus.Current.SpatialSpace d) := {x | ∀ i, x i ∈ Ioc 0 1}

def spatialCellMap {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) :
    OAI.Analysis.Calculus.Current.SpatialSpace d →L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d := (100 : ℝ) • R.toContinuousLinearMap

def physicalSpatialCell {d : ℕ} (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) : Set (OAI.Analysis.Calculus.Current.SpatialSpace d) :=
  spatialCellMap R '' spatialUnitCell d

theorem integral_spatialUnitCell {d : ℕ} (f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℝ) :
    (∫ x in spatialUnitCell d, f x) =
      ∫ q in {q : Option (Fin d) → ℝ | ∀ i, q i ∈ Ioc 0 1}, f (spatialFromCoordinates q) := by
  have hp := (PiLp.volume_preserving_ofLp (Option (Fin d))).setIntegral_preimage_emb
    (PiLp.homeomorph 2 (fun _ : Option (Fin d) => ℝ)).measurableEmbedding
    (fun q => f (spatialFromCoordinates q)) {q : Option (Fin d) → ℝ | ∀ i, q i ∈ Ioc 0 1}
  have hx (x : OAI.Analysis.Calculus.Current.SpatialSpace d) : spatialFromCoordinates x.ofLp = x := rfl
  simpa only [spatialUnitCell, hx] using! hp

theorem integral_physicalSpatialCell {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (f : OAI.Analysis.Calculus.Current.SpatialSpace d → ℝ) :
    (∫ x in physicalSpatialCell R, f x) =
      |LinearMap.det (spatialCellMap R).toLinearMap| *
        ∫ q in {q : Option (Fin d) → ℝ | ∀ i, q i ∈ Ioc 0 1},
          f ((100 : ℝ) • R (spatialFromCoordinates q)) := by
  have hi : Function.Injective (spatialCellMap R) := by
    intro x y he
    apply R.injective
    have hh := congrArg (fun z : OAI.Analysis.Calculus.Current.SpatialSpace d => (100 : ℝ)⁻¹ • z) he
    simpa [spatialCellMap, smul_smul] using hh
  have hs : MeasurableSet (spatialUnitCell d) := by
    unfold spatialUnitCell
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i : Option (Fin d) =>
      (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1)).preimage
        (EuclideanSpace.proj i : OAI.Analysis.Calculus.Current.SpatialSpace d →L[ℝ] ℝ).continuous.measurable
  have hJ := integral_image_eq_integral_abs_det_fderiv_smul volume
    (f := spatialCellMap R) (f' := fun _ => spatialCellMap R) (s := spatialUnitCell d)
    hs (fun x _ => (spatialCellMap R).hasFDerivAt.hasFDerivWithinAt) hi.injOn f
  rw [physicalSpatialCell, hJ]
  simp only [smul_eq_mul]
  rw [integral_const_mul, integral_spatialUnitCell]
  rfl

theorem integral_sq_physicalSpatialCell {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (ξ : ι → OAI.Analysis.Calculus.Current.SpatialSpace d)
    (m : ι → Option (Fin d) → ℤ) (hinj : Function.Injective m) (a : ι → ℂ)
    (hm : ∀ j i, inner ℝ (ξ j) (R (EuclideanSpace.single i 1)) = (m j i : ℝ) / 100) :
    (∫ x in physicalSpatialCell R, ‖finiteWave ξ a x‖ ^ 2) =
      |LinearMap.det (spatialCellMap R).toLinearMap| * ∑ i, ‖a i‖ ^ 2 := by
  rw [integral_physicalSpatialCell, integral_sq_spatialCoordinates R ξ m hinj a hm]

/-- Lebesgue-L² multiplier bound on the actual rotated side-100 cell.
The cell Jacobian cancels, so the constant is exactly the symbol supremum. -/
theorem physicalSpatialCell_multiplier_L2 {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (ξ : ι → OAI.Analysis.Calculus.Current.SpatialSpace d)
    (m : ι → Option (Fin d) → ℤ) (hinj : Function.Injective m) (a b : ι → ℂ)
    (hm : ∀ j i, inner ℝ (ξ j) (R (EuclideanSpace.single i 1)) = (m j i : ℝ) / 100)
    {B : ℝ} (hb : ∀ i, ‖b i‖ ≤ B) :
    (∫ x in physicalSpatialCell R, ‖finiteWave ξ (fun i => b i * a i) x‖ ^ 2) ≤
      B ^ 2 * ∫ x in physicalSpatialCell R, ‖finiteWave ξ a x‖ ^ 2 := by
  rw [integral_sq_physicalSpatialCell R ξ m hinj _ hm,
    integral_sq_physicalSpatialCell R ξ m hinj a hm]
  have hs : (∑ i, ‖b i * a i‖ ^ 2) ≤ B ^ 2 * ∑ i, ‖a i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb i) 2) (sq_nonneg _)
  simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hs
    (abs_nonneg (LinearMap.det (spatialCellMap R).toLinearMap))

end OAI.Analysis.PDE.Concentration
