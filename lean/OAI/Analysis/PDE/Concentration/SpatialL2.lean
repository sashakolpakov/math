import OAI.Analysis.PDE.Concentration.TorusL2
import OAI.Analysis.PDE.Concentration.FourierPeriodicity

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current _root_.MeasureTheory Set
open scoped ComplexConjugate

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def torusIndexedWave {D ι : Type*} [Fintype D] [Fintype ι]
    (m : ι → D → ℤ) (a : ι → ℂ) : C(UnitAddTorus D, ℂ) :=
  ∑ i, a i • UnitAddTorus.mFourier (m i)

theorem integral_sq_torusIndexedWave {D ι : Type*} [Fintype D] [Fintype ι]
    (m : ι → D → ℤ) (hm : Function.Injective m) (a : ι → ℂ) :
    (∫ x, ‖torusIndexedWave m a x‖ ^ 2) = ∑ i, ‖a i‖ ^ 2 := by
  let f := torusIndexedWave m a
  have hf : Integrable (fun x => f x * conj (f x)) :=
    (f.continuous.mul f.continuous.star).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : inner ℂ (ContinuousMap.toLp 2 volume ℂ f) (ContinuousMap.toLp 2 volume ℂ f) =
      ∑ i, conj (a i) * a i := by
    have ho := UnitAddTorus.orthonormal_mFourier.comp m hm
    simpa only [f, torusIndexedWave, map_sum, map_smul, Function.comp_apply] using!
      ho.inner_sum a a Finset.univ
  rw [ContinuousMap.inner_toLp] at he
  have hr := congrArg (RCLike.re : ℂ → ℝ) he
  rw [← integral_re hf] at hr
  have hre (z : ℂ) : (conj z * z).re = ‖z‖ ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simpa only [Complex.mul_conj, Complex.ofReal_re, RCLike.re_to_complex, map_sum,
    Complex.normSq_eq_norm_sq, hre] using hr

theorem mFourier_coe_eq_exp {D : Type*} [Fintype D] (m : D → ℤ) (x : D → ℝ) :
    UnitAddTorus.mFourier m (fun i => (x i : UnitAddCircle)) =
      Complex.exp (((2 * Real.pi * ∑ i, (m i : ℝ) * x i : ℝ) : ℂ) * Complex.I) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

def spatialFromCoordinates {d : ℕ} (x : Option (Fin d) → ℝ) : OAI.Analysis.Calculus.Current.SpatialSpace d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin d) => ℝ)).symm x

theorem spatialFromCoordinates_eq_sum {d : ℕ} (x : Option (Fin d) → ℝ) :
    spatialFromCoordinates x = ∑ i, x i • EuclideanSpace.single i 1 := by
  ext j
  cases j with
  | none => simp [spatialFromCoordinates]
  | some j => simp [spatialFromCoordinates, Pi.single_apply]

theorem planeWave_spatialCoordinates {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (ξ : OAI.Analysis.Calculus.Current.SpatialSpace d) (m : Option (Fin d) → ℤ)
    (hm : ∀ i, inner ℝ ξ (R (EuclideanSpace.single i 1)) = (m i : ℝ) / 100)
    (x : Option (Fin d) → ℝ) :
    planeWave ξ ((100 : ℝ) • R (spatialFromCoordinates x)) =
      UnitAddTorus.mFourier m (fun i => (x i : UnitAddCircle)) := by
  have hi : inner ℝ ((100 : ℝ) • R (spatialFromCoordinates x)) ξ = ∑ i, (m i : ℝ) * x i := by
    rw [real_inner_comm, inner_smul_right, spatialFromCoordinates_eq_sum, map_sum, inner_sum]
    simp only [map_smul, inner_smul_right, hm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [planeWave, hi, mFourier_coe_eq_exp]

theorem finiteWave_spatialCoordinates {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (ξ : ι → OAI.Analysis.Calculus.Current.SpatialSpace d)
    (m : ι → Option (Fin d) → ℤ) (a : ι → ℂ)
    (hm : ∀ j i, inner ℝ (ξ j) (R (EuclideanSpace.single i 1)) = (m j i : ℝ) / 100)
    (x : Option (Fin d) → ℝ) :
    finiteWave ξ a ((100 : ℝ) • R (spatialFromCoordinates x)) =
      torusIndexedWave m a (fun i => (x i : UnitAddCircle)) := by
  simp only [finiteWave, torusIndexedWave, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [planeWave_spatialCoordinates R (ξ j) (m j) (hm j)]

theorem integral_sq_spatialCoordinates {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (ξ : ι → OAI.Analysis.Calculus.Current.SpatialSpace d)
    (m : ι → Option (Fin d) → ℤ) (hinj : Function.Injective m) (a : ι → ℂ)
    (hm : ∀ j i, inner ℝ (ξ j) (R (EuclideanSpace.single i 1)) = (m j i : ℝ) / 100) :
    (∫ x in {x : Option (Fin d) → ℝ | ∀ i, x i ∈ Ioc 0 1},
      ‖finiteWave ξ a ((100 : ℝ) • R (spatialFromCoordinates x))‖ ^ 2) = ∑ i, ‖a i‖ ^ 2 := by
  rw [← integral_sq_torusIndexedWave m hinj a,
    UnitAddTorus.integral_preimage (fun x => ‖torusIndexedWave m a x‖ ^ 2) (fun _ => 0)]
  simp only [zero_add]
  apply setIntegral_congr_fun (MeasurableSet.univ_pi' fun _ => measurableSet_Ioc)
  intro x _
  dsimp only
  rw [finiteWave_spatialCoordinates R ξ m a hm]

end OAI.Analysis.PDE.Concentration
