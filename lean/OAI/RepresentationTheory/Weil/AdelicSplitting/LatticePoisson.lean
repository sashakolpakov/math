import OAI.RepresentationTheory.Weil.AdelicSplitting.LatticeDualCoordinates
import OAI.RepresentationTheory.Theta.RealPoisson

/-! # Lattice Poisson -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson.LocalAnalysis

noncomputable section

/-! Real lattice Poisson summation for an arbitrary nondegenerate bilinear
pairing and Haar measure. The measure factor is explicitly positive. -/

open _root_.MeasureTheory
open scoped Classical NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
  (B : LinearMap.BilinForm ℝ E) (μ : Measure E) [μ.IsAddHaarMeasure]

def realBilinearFourier (f : E → ℂ) (x : E) : ℂ :=
  ∫ y, f y * RealCharacters.LocalAnalysis.realCharacter 1 (-(B x y)) ∂μ

def basisHaarFactor : ℝ≥0 :=
  Measure.addHaarScalarFactor (μ.map b.equivFunL) volume

theorem basisHaarFactor_pos : 0 < basisHaarFactor b μ := by
  let : (μ.map b.equivFunL).IsAddHaarMeasure := b.equivFunL.isAddHaarMeasure_map μ
  exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem realBilinearFourier_coordinates_fun (hB : B.SeparatingLeft)
    (f : E → ℂ) (ξ : ι → ℝ) :
    realBilinearFourier B μ f ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm ξ) =
      (basisHaarFactor b μ : ℂ) * Theta.PoissonAutomorphyNormalizationData.fourier Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume
        (fun y => f (b.equivFunL.symm y)) ξ := by
  let e := b.equivFunL
  let : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hm : μ.map e = basisHaarFactor b μ • volume :=
    Measure.isAddLeftInvariant_eq_smul_of_regular _ _
  calc
    _ = ∫ t, f (e.symm t) * RealCharacters.LocalAnalysis.realCharacter 1
        (-(B ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm ξ) (e.symm t))) ∂(μ.map e) := by
      have hh := e.toHomeomorph.isClosedEmbedding.integral_map (μ := μ)
        (fun t => f (e.symm t) * RealCharacters.LocalAnalysis.realCharacter 1
          (-(B ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm ξ) (e.symm t))))
      have he : (e.toHomeomorph : E → (ι → ℝ)) = e := rfl
      rw [he] at hh
      simpa only [e.symm_apply_apply, realBilinearFourier] using! hh.symm
    _ = _ := by
      rw [hm, integral_smul_nnreal_measure]
      change (basisHaarFactor b μ : ℂ) *
        (∫ t, f (e.symm t) * RealCharacters.LocalAnalysis.realCharacter 1
          (-(B ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm ξ) (e.symm t)))) = _
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        have h := LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates_pairing b B hB ξ t
        change B ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm ξ) (e.symm t) = _ at h
        change f (e.symm t) * RealCharacters.LocalAnalysis.realCharacter 1
          (-(B ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm ξ) (e.symm t))) =
            f (e.symm t) * Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(∑ i, ξ i * t i))
        rw [h]
        simp only [RealCharacters.LocalAnalysis.realCharacter_apply, Theta.PoissonAutomorphyNormalizationData.standardRealCharacter_apply, mul_one]

theorem realBilinearFourier_coordinates (hB : B.SeparatingLeft)
    (f : SchwartzMap E ℂ) (ξ : ι → ℝ) :
    realBilinearFourier B μ f ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm ξ) =
      (basisHaarFactor b μ : ℂ) * Theta.PoissonAutomorphyNormalizationData.fourier Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ b.equivFunL.symm f) ξ :=
  realBilinearFourier_coordinates_fun b B μ hB f ξ

theorem real_lattice_poisson_positive (hB : B.SeparatingLeft)
    (f : SchwartzMap E ℂ) :
    (∑' n : ι → ℤ, realBilinearFourier B μ f
      ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm (fun i => (n i : ℝ)))) =
      (basisHaarFactor b μ : ℂ) *
        ∑' n : ι → ℤ, f (b.equivFunL.symm (fun i => (n i : ℝ))) := by
  simp_rw [realBilinearFourier_coordinates b B μ hB f]
  rw [tsum_mul_left]
  congr 1
  exact (Theta.RealPoisson.AutomorphyConstruction.real_poisson_summation
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ b.equivFunL.symm f)).symm

theorem real_lattice_poisson_shift_positive (hB : B.SeparatingLeft)
    (f : SchwartzMap E ℂ) (a : E) :
    (∑' n : ι → ℤ, realBilinearFourier B μ f
      ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm (fun i => (n i : ℝ))) *
      RealCharacters.LocalAnalysis.realCharacter 1 (B ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm (fun i => (n i : ℝ))) a)) =
      (basisHaarFactor b μ : ℂ) *
        ∑' n : ι → ℤ, f (a + b.equivFunL.symm (fun i => (n i : ℝ))) := by
  have hphase (n : ι → ℤ) :
      RealCharacters.LocalAnalysis.realCharacter 1 (B ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm (fun i => (n i : ℝ))) a) =
        Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (∑ i, (n i : ℝ) * b.equivFun a i) := by
    have hh := LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates_pairing b B hB (fun i => (n i : ℝ)) (b.equivFun a)
    rw [b.equivFun.symm_apply_apply] at hh
    rw [hh]
    simp only [RealCharacters.LocalAnalysis.realCharacter_apply, Theta.PoissonAutomorphyNormalizationData.standardRealCharacter_apply, mul_one]
  simp_rw [realBilinearFourier_coordinates b B μ hB f, hphase, mul_assoc]
  rw [tsum_mul_left]
  congr 1
  have hp := Theta.RealPoisson.AutomorphyConstruction.real_poisson_summation_shift
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ b.equivFunL.symm f) (b.equivFun a)
  convert hp.symm using 1
  · rfl
  · apply tsum_congr
    intro n
    change f (a + b.equivFunL.symm (fun i => (n i : ℝ))) =
      f (b.equivFunL.symm (b.equivFun a + (fun i => (n i : ℝ))))
    rw [map_add b.equivFunL.symm]
    have ha : b.equivFunL.symm (b.equivFun a) = a := b.equivFun.symm_apply_apply a
    rw [ha]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.LatticePoisson.LocalAnalysis
