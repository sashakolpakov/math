import OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions
import OAI.RepresentationTheory.Theta.RealPoisson

/-! # Rapid Poisson -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RapidPoisson.LocalAnalysis

noncomputable section

/-! Poisson summation from continuous rapid decay and summability of the
sampled Fourier transform. This form applies to finite products of local
Schwartz functions without imposing a separate joint derivative estimate. -/

open scoped Classical
open _root_.MeasureTheory OAI.RepresentationTheory.Theta.RealPoisson.AutomorphyConstruction

variable {ι : Type*} [Fintype ι]

theorem rapidLatticePeriodization_eq_of_projection_eq (f : RapidFunctions.LocalAnalysis.RapidFunction (ι → ℝ))
    {x y : ι → ℝ} (h : Theta.RealFourier.PoissonAutomorphyConstruction.torusProjection x = Theta.RealFourier.PoissonAutomorphyConstruction.torusProjection y) :
    RapidFunctions.LocalAnalysis.rapidLatticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f x =
      RapidFunctions.LocalAnalysis.rapidLatticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f y := by
  let a : AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι := ⟨x - y, (Theta.RealFourier.PoissonAutomorphyConstruction.torusProjection_eq_iff x y).mp h⟩
  have hxy : x = y + a.val := by dsimp [a]; abel
  rw [hxy]
  exact RapidFunctions.LocalAnalysis.rapidLatticePeriodization_add _ f a y

def rapidTorusPeriodization (f : RapidFunctions.LocalAnalysis.RapidFunction (ι → ℝ)) : C(UnitAddTorus ι, ℂ) where
  toFun t := RapidFunctions.LocalAnalysis.rapidLatticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f (Theta.RealFourier.PoissonAutomorphyConstruction.torusRepresentative t)
  continuous_toFun := by
    apply Theta.RealFourier.PoissonAutomorphyConstruction.torusProjection_isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
    have heq : (fun x : ι → ℝ =>
        RapidFunctions.LocalAnalysis.rapidLatticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f
          (Theta.RealFourier.PoissonAutomorphyConstruction.torusRepresentative (Theta.RealFourier.PoissonAutomorphyConstruction.torusProjection x))) =
        RapidFunctions.LocalAnalysis.rapidLatticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f := by
      funext x
      exact rapidLatticePeriodization_eq_of_projection_eq f (Theta.RealFourier.PoissonAutomorphyConstruction.torusRepresentative_projection _)
    change Continuous (fun x : ι → ℝ => _)
    simp only [Function.comp_def]
    rw [heq]
    exact (RapidFunctions.LocalAnalysis.rapidLatticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f).continuous

theorem rapidTorusPeriodization_projection (f : RapidFunctions.LocalAnalysis.RapidFunction (ι → ℝ)) (x : ι → ℝ) :
    rapidTorusPeriodization f (Theta.RealFourier.PoissonAutomorphyConstruction.torusProjection x) = ∑' n : ι → ℤ, f (x + Theta.RealFourier.PoissonAutomorphyConstruction.integerReal n) := by
  change RapidFunctions.LocalAnalysis.rapidLatticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f
    (Theta.RealFourier.PoissonAutomorphyConstruction.torusRepresentative (Theta.RealFourier.PoissonAutomorphyConstruction.torusProjection x)) = _
  rw [rapidLatticePeriodization_eq_of_projection_eq f (Theta.RealFourier.PoissonAutomorphyConstruction.torusRepresentative_projection _),
    RapidFunctions.LocalAnalysis.rapidLatticePeriodization_apply]
  exact (Theta.RealFourier.PoissonAutomorphyConstruction.integerLatticeEquiv.tsum_eq (fun a : AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι => f (x + a.val))).symm

theorem rapidTorusPeriodization_fourierCoeff (f : RapidFunctions.LocalAnalysis.RapidFunction (ι → ℝ)) (hf : Integrable (fun x => f x)) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (rapidTorusPeriodization f) n =
      ∫ x : ι → ℝ, UnitAddTorus.mFourier (-n) (Theta.RealFourier.PoissonAutomorphyConstruction.torusProjection x) * f x := by
  let e : (ι → ℝ) → ℂ := fun x => UnitAddTorus.mFourier (-n) (Theta.RealFourier.PoissonAutomorphyConstruction.torusProjection x)
  have he : Continuous e := (UnitAddTorus.mFourier (-n)).continuous.comp
    Theta.RealFourier.PoissonAutomorphyConstruction.torusProjection_isOpenQuotientMap.continuous
  have henorm (x : ι → ℝ) : ‖e x‖ = 1 := Theta.PeriodizationIntegral.PoissonAutomorphyConstruction.mFourier_apply_norm _ _
  have hF : Integrable (fun x => e x * f x) := by
    apply hf.norm.mono' (he.mul f.continuous).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply, norm_mul, henorm, one_mul, le_refl]
  have hshift (x : ι → ℝ) (a : AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) : e (x + a.val) = e x := by
    dsimp [e]
    rw [Theta.PeriodizationIntegral.PoissonAutomorphyConstruction.torusProjection_add_lattice]
  rw [UnitAddTorus.mFourierCoeff]
  calc
    _ = ∫ x in Theta.PeriodizationIntegral.PoissonAutomorphyConstruction.unitCube, e x * rapidTorusPeriodization f (Theta.RealFourier.PoissonAutomorphyConstruction.torusProjection x) := by
      simpa only [smul_eq_mul] using Theta.PeriodizationIntegral.PoissonAutomorphyConstruction.torus_integral_unitCube
        (fun t => UnitAddTorus.mFourier (-n) t • rapidTorusPeriodization f t)
    _ = ∫ x in Theta.PeriodizationIntegral.PoissonAutomorphyConstruction.unitCube, ∑' a : AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι, e (x + a.val) * f (x + a.val) := by
      apply setIntegral_congr_fun (by rw [Theta.PeriodizationIntegral.PoissonAutomorphyConstruction.unitCube_eq_fundamentalDomain]; exact
        ZSpan.fundamentalDomain_measurableSet (Pi.basisFun ℝ ι))
      intro x _
      simp only [hshift, tsum_mul_left]
      congr 1
      change RapidFunctions.LocalAnalysis.rapidLatticePeriodization (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f
        (Theta.RealFourier.PoissonAutomorphyConstruction.torusRepresentative (Theta.RealFourier.PoissonAutomorphyConstruction.torusProjection x)) = _
      rw [rapidLatticePeriodization_eq_of_projection_eq f (Theta.RealFourier.PoissonAutomorphyConstruction.torusRepresentative_projection _),
        RapidFunctions.LocalAnalysis.rapidLatticePeriodization_apply]
    _ = _ := Theta.PeriodizationIntegral.PoissonAutomorphyConstruction.integral_lattice_periodization hF

theorem rapid_real_poisson_shift (f : RapidFunctions.LocalAnalysis.RapidFunction (ι → ℝ))
    (hf : Integrable (fun x => f x))
    (hF : Summable (fun n : ι → ℤ =>
      Theta.PoissonAutomorphyNormalizationData.fourier Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume f (Theta.RealFourier.PoissonAutomorphyConstruction.integerReal n)))
    (x : ι → ℝ) :
    (∑' n : ι → ℤ, f (x + Theta.RealFourier.PoissonAutomorphyConstruction.integerReal n)) =
      ∑' n : ι → ℤ, Theta.PoissonAutomorphyNormalizationData.fourier Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume f (Theta.RealFourier.PoissonAutomorphyConstruction.integerReal n) *
        Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (∑ i, (n i : ℝ) * x i) := by
  have hcoeff (n : ι → ℤ) :
      UnitAddTorus.mFourierCoeff (rapidTorusPeriodization f) n =
        Theta.PoissonAutomorphyNormalizationData.fourier Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume f (Theta.RealFourier.PoissonAutomorphyConstruction.integerReal n) := by
    rw [rapidTorusPeriodization_fourierCoeff f hf, Theta.PoissonAutomorphyNormalizationData.fourier]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp only
      rw [Theta.RealPoisson.AutomorphyConstruction.mFourier_projection]
      simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, Theta.RealFourier.PoissonAutomorphyConstruction.integerReal]
      exact mul_comm _ _
  have hsum : Summable (UnitAddTorus.mFourierCoeff (rapidTorusPeriodization f)) :=
    hF.congr (fun n => (hcoeff n).symm)
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum (Theta.RealFourier.PoissonAutomorphyConstruction.torusProjection x)
  simpa only [rapidTorusPeriodization_projection, hcoeff, smul_eq_mul, Theta.RealPoisson.AutomorphyConstruction.mFourier_projection]
    using h.tsum_eq.symm

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RapidPoisson.LocalAnalysis
