import OAI.Analysis.Fourier.Dispersion.LinearFourier

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

open _root_.MeasureTheory
open scoped ENNReal

def linearJacobian {n : ℕ} (A : Space n ≃L[ℝ] Space n) : ℝ≥0∞ :=
  ENNReal.ofReal |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹|

theorem linearJacobian_ne_zero {n : ℕ} (A : Space n ≃L[ℝ] Space n) :
    linearJacobian A ≠ 0 := by
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  exact abs_pos.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)

theorem linearJacobian_ne_top {n : ℕ} (A : Space n ≃L[ℝ] Space n) :
    linearJacobian A ≠ ∞ := ENNReal.ofReal_ne_top

theorem map_volume_linearEquiv {n : ℕ} (A : Space n ≃L[ℝ] Space n) :
    Measure.map A volume = linearJacobian A • volume :=
  Measure.map_linearMap_addHaar_eq_smul_addHaar volume A.toLinearEquiv.isUnit_det'.ne_zero

theorem map_observation_linearEquiv {n : ℕ} (A : Space n ≃L[ℝ] Space n) :
    Measure.map (fun z : Space n × ℝ => (A z.1,z.2)) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) =
      linearJacobian A • OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n := by
  change Measure.map (Prod.map A id) (volume.prod (volume.restrict (Set.Icc 1 2))) = _
  rw [← Measure.map_prod_map volume (volume.restrict (Set.Icc 1 2)) A.continuous.measurable measurable_id,
    Measure.map_id,map_volume_linearEquiv,Measure.prod_smul_left]
  rfl

theorem eLpNorm_comp_linearEquiv {n : ℕ} (A : Space n ≃L[ℝ] Space n)
    (f : Space n → ℂ) (p : ℝ≥0∞) :
    eLpNorm (f ∘ A) p volume = (linearJacobian A) ^ (1/p).toReal * eLpNorm f p volume := by
  have he : eLpNorm f p (Measure.map A volume) = eLpNorm (f ∘ A) p volume :=
    A.toHomeomorph.measurableEmbedding.eLpNorm_map_measure
  rw [← he,map_volume_linearEquiv,
    eLpNorm_smul_measure_of_ne_zero (linearJacobian_ne_zero A)]
  rfl

theorem eLpNorm_observation_comp_linearEquiv {n : ℕ} (A : Space n ≃L[ℝ] Space n)
    (f : Space n × ℝ → ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun z : Space n × ℝ => f (A z.1,z.2)) p (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) =
      (linearJacobian A) ^ (1/p).toReal * eLpNorm f p (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := by
  let T := A.toHomeomorph.prodCongr (Homeomorph.refl ℝ)
  change eLpNorm (f ∘ T) p (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) = _
  rw [← T.measurableEmbedding.eLpNorm_map_measure]
  change eLpNorm f p (Measure.map (fun z : Space n × ℝ => (A z.1,z.2)) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n)) = _
  rw [map_observation_linearEquiv,eLpNorm_smul_measure_of_ne_zero (linearJacobian_ne_zero A)]
  rfl

end OAI.Analysis.Fourier.Dispersion
