import OAI.RepresentationTheory.Weil.AdelicSplitting.RapidPoisson
import OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions
import OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson

/-! # Rapid Lattice Poisson -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RapidLatticePoisson.LocalAnalysis

noncomputable section

/-! Shifted lattice Poisson summation when a function and its actual
bilinear Fourier transform are continuous and rapidly decreasing. -/

open scoped Classical
open _root_.MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
  (B : LinearMap.BilinForm ℝ E) (μ : Measure E) [μ.IsAddHaarMeasure]

theorem rapid_integer_summable_norm (f : RapidFunctions.LocalAnalysis.RapidFunction (ι → ℝ)) :
    Summable (fun n : ι → ℤ => ‖f (Theta.RealFourier.PoissonAutomorphyConstruction.integerReal n)‖) := by
  have hh := (RapidFunctions.LocalAnalysis.rapid_lattice_summable_norm (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι) f 0).comp_injective
    (Theta.RealFourier.PoissonAutomorphyConstruction.integerLatticeEquiv (ι := ι)).injective
  simpa only [Function.comp_def, zero_add, Theta.RealFourier.PoissonAutomorphyConstruction.integerLatticeEquiv_apply] using hh

theorem rapid_lattice_poisson_shift_positive (hB : B.SeparatingLeft)
    (f g : RapidFunctions.LocalAnalysis.RapidFunction E) (hfg : ∀ x, g x = LatticePoisson.LocalAnalysis.realBilinearFourier B μ f x) (a : E) :
    (∑' n : ι → ℤ, g ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm (fun i => (n i : ℝ))) *
      RealCharacters.LocalAnalysis.realCharacter 1 (B ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm (fun i => (n i : ℝ))) a)) =
      (LatticePoisson.LocalAnalysis.basisHaarFactor b μ : ℂ) *
        ∑' n : ι → ℤ, f (a + b.equivFunL.symm (fun i => (n i : ℝ))) := by
  let f' := f.compLinearEquiv b.equivFunL.symm
  let g' := g.compLinearEquiv (LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm
  have hg' := (rapid_integer_summable_norm g').of_norm
  have hr : (LatticePoisson.LocalAnalysis.basisHaarFactor b μ : ℂ) ≠ 0 := by
    exact_mod_cast (LatticePoisson.LocalAnalysis.basisHaarFactor_pos b μ).ne'
  have hF (ξ : ι → ℝ) : Theta.PoissonAutomorphyNormalizationData.fourier Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume f' ξ =
      (LatticePoisson.LocalAnalysis.basisHaarFactor b μ : ℂ)⁻¹ * g' ξ := by
    have hh := LatticePoisson.LocalAnalysis.realBilinearFourier_coordinates_fun b B μ hB f ξ
    rw [← hfg] at hh
    change g' ξ = (LatticePoisson.LocalAnalysis.basisHaarFactor b μ : ℂ) * Theta.PoissonAutomorphyNormalizationData.fourier Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume f' ξ at hh
    rw [hh, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]
  have hs : Summable (fun n : ι → ℤ => Theta.PoissonAutomorphyNormalizationData.fourier Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume f' (Theta.RealFourier.PoissonAutomorphyConstruction.integerReal n)) := by
    simp_rw [hF]
    exact hg'.mul_left _
  have hp := RapidPoisson.LocalAnalysis.rapid_real_poisson_shift f' (f'.integrable volume) hs (b.equivFun a)
  have hphase (n : ι → ℤ) :
      RealCharacters.LocalAnalysis.realCharacter 1 (B ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm (fun i => (n i : ℝ))) a) =
        Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (∑ i, (n i : ℝ) * b.equivFun a i) := by
    have hh := LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates_pairing b B hB (fun i => (n i : ℝ)) (b.equivFun a)
    rw [b.equivFun.symm_apply_apply] at hh
    rw [hh]
    simp only [RealCharacters.LocalAnalysis.realCharacter_apply, Theta.PoissonAutomorphyNormalizationData.standardRealCharacter_apply, mul_one]
  have hcoef (n : ι → ℤ) : g ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm (fun i => (n i : ℝ))) =
      (LatticePoisson.LocalAnalysis.basisHaarFactor b μ : ℂ) * Theta.PoissonAutomorphyNormalizationData.fourier Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume f' (Theta.RealFourier.PoissonAutomorphyConstruction.integerReal n) :=
    (hfg _).trans (LatticePoisson.LocalAnalysis.realBilinearFourier_coordinates_fun b B μ hB f _)
  simp_rw [hcoef, hphase, mul_assoc]
  rw [tsum_mul_left]
  congr 1
  calc
    _ = ∑' n : ι → ℤ, f' (b.equivFun a + Theta.RealFourier.PoissonAutomorphyConstruction.integerReal n) := hp.symm
    _ = _ := by
      apply tsum_congr
      intro n
      change f (b.equivFunL.symm (b.equivFun a + Theta.RealFourier.PoissonAutomorphyConstruction.integerReal n)) =
        f (a + b.equivFunL.symm (fun i => (n i : ℝ)))
      rw [map_add b.equivFunL.symm]
      have ha : b.equivFunL.symm (b.equivFun a) = a := b.equivFun.symm_apply_apply a
      rw [ha]
      rfl

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RapidLatticePoisson.LocalAnalysis
