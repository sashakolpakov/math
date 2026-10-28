import OAI.RepresentationTheory.Theta.RealFourier

/-! # Periodization Integral -/

namespace OAI.RepresentationTheory.Theta.PeriodizationIntegral.PoissonAutomorphyConstruction

noncomputable section

/-! Integration of lattice periodizations over the unit cube. -/

open scoped Classical ENNReal
open _root_.MeasureTheory

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {ι : Type*} [Fintype ι]

def unitCube : Set (ι → ℝ) := {x | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1}

theorem unitCube_eq_fundamentalDomain : unitCube (ι := ι) =
    ZSpan.fundamentalDomain (Pi.basisFun ℝ ι) := by
  ext x
  simp [unitCube, ZSpan.mem_fundamentalDomain]

theorem integral_lattice_periodization {f : (ι → ℝ) → ℂ} (hf : Integrable f) :
    (∫ x in unitCube, ∑' a : AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι, f (x + a.val)) = ∫ x, f x := by
  let : Countable (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) :=
    Countable.of_equiv (ι → ℤ) (RealFourier.PoissonAutomorphyConstruction.integerLatticeEquiv (ι := ι))
  let : VAddInvariantMeasure (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (ι → ℝ) volume :=
    inferInstanceAs (VAddInvariantMeasure (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι).toAddSubgroup (ι → ℝ) volume)
  have hFD : IsAddFundamentalDomain (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (unitCube (ι := ι)) volume := by
    rw [unitCube_eq_fundamentalDomain]
    exact ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) volume
  have heq : ∑' a : AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι,
      ∫⁻ x in unitCube, ‖f (x + a.val)‖ₑ = ∫⁻ x, ‖f x‖ₑ := by
    have h := hFD.lintegral_eq_tsum'' (fun x => ‖f x‖ₑ)
    simpa only [Submodule.vadd_def, vadd_eq_add, add_comm] using h.symm
  rw [integral_tsum (f := fun (a : AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) (x : ι → ℝ) => f (x + a.val))
    (fun a => (hf.comp_add_right a.val).restrict.aestronglyMeasurable)
    (heq.trans_ne hf.hasFiniteIntegral.ne)]
  have h := hFD.integral_eq_tsum'' f hf
  simpa only [Submodule.vadd_def, vadd_eq_add, add_comm] using h.symm

theorem unitCube_ae_eq_Ioc : unitCube (ι := ι) =ᵐ[volume]
    {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} := by
  have h := Measure.ae_eq_set_pi (μ := fun _ : ι => (volume : Measure ℝ))
    (I := Set.univ) (fun _ _ => (Ico_ae_eq_Ioc : Set.Ico (0 : ℝ) 1 =ᵐ[volume] Set.Ioc 0 1))
  simpa only [← volume_pi, Set.pi, Set.mem_univ, forall_const, unitCube] using h

theorem torus_integral_unitCube (f : UnitAddTorus ι → ℂ) :
    (∫ x, f x) = ∫ x in unitCube, f (RealFourier.PoissonAutomorphyConstruction.torusProjection x) := by
  calc
    _ = ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}, f (RealFourier.PoissonAutomorphyConstruction.torusProjection x) := by
      convert UnitAddTorus.integral_preimage f (0 : ι → ℝ) using 1
      simp only [Pi.zero_apply, zero_add]
      rfl
    _ = _ := setIntegral_congr_set (unitCube_ae_eq_Ioc (ι := ι)).symm

theorem mFourier_apply_norm (n : ι → ℤ) (t : UnitAddTorus ι) :
    ‖UnitAddTorus.mFourier n t‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
    fourier_apply, Circle.norm_coe, Finset.prod_const_one]

theorem torusProjection_add_lattice (x : ι → ℝ) (a : AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) :
    RealFourier.PoissonAutomorphyConstruction.torusProjection (x + a.val) = RealFourier.PoissonAutomorphyConstruction.torusProjection x := by
  apply (RealFourier.PoissonAutomorphyConstruction.torusProjection_eq_iff _ _).mpr
  simpa only [add_sub_cancel_left] using a.property

theorem torusPeriodization_fourierCoeff (f : SchwartzMap (ι → ℝ) ℂ) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (RealFourier.PoissonAutomorphyConstruction.torusPeriodization f) n =
      ∫ x : ι → ℝ, UnitAddTorus.mFourier (-n) (RealFourier.PoissonAutomorphyConstruction.torusProjection x) * f x := by
  let e : (ι → ℝ) → ℂ := fun x => UnitAddTorus.mFourier (-n) (RealFourier.PoissonAutomorphyConstruction.torusProjection x)
  have he : Continuous e := (UnitAddTorus.mFourier (-n)).continuous.comp
    RealFourier.PoissonAutomorphyConstruction.torusProjection_isOpenQuotientMap.continuous
  have henorm (x : ι → ℝ) : ‖e x‖ = 1 := mFourier_apply_norm _ _
  have hF : Integrable (fun x => e x * f x) := by
    apply f.integrable.norm.mono' (he.mul f.continuous).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply, norm_mul, henorm, one_mul, le_refl]
  have hshift (x : ι → ℝ) (a : AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) : e (x + a.val) = e x := by
    dsimp [e]
    rw [torusProjection_add_lattice]
  rw [UnitAddTorus.mFourierCoeff]
  calc
    _ = ∫ x in unitCube, e x * RealFourier.PoissonAutomorphyConstruction.torusPeriodization f (RealFourier.PoissonAutomorphyConstruction.torusProjection x) := by
      simpa only [smul_eq_mul] using torus_integral_unitCube
        (fun t => UnitAddTorus.mFourier (-n) t • RealFourier.PoissonAutomorphyConstruction.torusPeriodization f t)
    _ = ∫ x in unitCube, ∑' a : AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι, e (x + a.val) * f (x + a.val) := by
      apply setIntegral_congr_fun (by rw [unitCube_eq_fundamentalDomain]; exact
        ZSpan.fundamentalDomain_measurableSet (Pi.basisFun ℝ ι))
      intro x _
      simp only [hshift, tsum_mul_left]
      congr 1
      change PoissonAutomorphyNormalizationData.Construction.latticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f
        (RealFourier.PoissonAutomorphyConstruction.torusRepresentative (RealFourier.PoissonAutomorphyConstruction.torusProjection x)) = _
      rw [RealFourier.PoissonAutomorphyConstruction.latticePeriodization_eq_of_projection_eq f (RealFourier.PoissonAutomorphyConstruction.torusRepresentative_projection _),
        PoissonAutomorphyNormalizationData.Construction.latticePeriodization_apply]
    _ = _ := integral_lattice_periodization hF

end

end OAI.RepresentationTheory.Theta.PeriodizationIntegral.PoissonAutomorphyConstruction
