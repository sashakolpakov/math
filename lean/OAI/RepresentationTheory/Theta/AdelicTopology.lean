import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Adelic Topology -/

namespace OAI.RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction

noncomputable section

section

/-! Local compactness needed for Haar product integration. -/

instance finiteAdeleLocallyCompact : LocallyCompactSpace PoissonAutomorphyNormalizationData.AQf :=
  IntegralAdeles.PoissonAutomorphyConstruction.isCompact_integralAdele.locallyCompactSpace_of_mem_nhds_of_addGroup
    (AdelicSupport.PoissonAutomorphyConstruction.isOpen_integralAdele.mem_nhds AdelicSupport.PoissonAutomorphyConstruction.integralAdele.zero_mem)

end

/-! Separation of the real and finite Fourier integrals. -/

open scoped Classical
open _root_.MeasureTheory

variable {ι : Type*}

def adelicProductEquiv : ((ι → ℝ) × (ι → PoissonAutomorphyNormalizationData.AQf)) ≃ᵐ (ι → PoissonAutomorphyNormalizationData.AQ) where
  toFun x i := (x.1 i, x.2 i)
  invFun x := (fun i => (x i).1, fun i => (x i).2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := Measurable.of_eval (fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  measurable_invFun := (Measurable.of_eval (fun i =>
    measurable_fst.comp (measurable_pi_apply i))).prodMk
      (Measurable.of_eval (fun i => measurable_snd.comp (measurable_pi_apply i)))

variable [Fintype ι] [DecidableEq ι]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem adelic_fourier_tensor_function (f : (ι → ℝ) → ℂ) (φ : (ι → PoissonAutomorphyNormalizationData.AQf) → ℂ)
    (x : ι → PoissonAutomorphyNormalizationData.AQ) :
    PoissonAutomorphyNormalizationData.fourier D.character (PoissonAutomorphyNormalizationData.adelicMeasure D.finiteMeasure)
      (fun y => f (fun i => (y i).1) * φ (fun i => (y i).2)) x =
        PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume f (fun i => (x i).1) *
          PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure φ (fun i => (x i).2) := by
  let := D.finiteMeasure_haar
  change (∫ y, (f (fun i => (y i).1) * φ (fun i => (y i).2)) *
    D.character (-(∑ i, x i * y i)) ∂Measure.map adelicProductEquiv (volume.prod D.finiteMeasure)) = _
  rw [adelicProductEquiv.measurableEmbedding.integral_map]
  calc
    _ = ∫ y : (ι → ℝ) × (ι → PoissonAutomorphyNormalizationData.AQf),
        (f y.1 * PoissonAutomorphyNormalizationData.standardRealCharacter (-(∑ i, (x i).1 * y.1 i))) *
          (φ y.2 * D.finiteCharacter (-(∑ i, (x i).2 * y.2 i))) ∂volume.prod D.finiteMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change (f y.1 * φ y.2) * D.character (-(∑ i, x i * (y.1 i, y.2 i))) = _
        have heq : -(∑ i, x i * (y.1 i, y.2 i)) =
            (-(∑ i, (x i).1 * y.1 i), -(∑ i, (x i).2 * y.2 i)) := by
          apply Prod.ext
          · change -((RingHom.fst ℝ PoissonAutomorphyNormalizationData.AQf) (∑ i, x i * (y.1 i, y.2 i))) = _
            rw [map_sum]
            rfl
          · change -((RingHom.snd ℝ PoissonAutomorphyNormalizationData.AQf) (∑ i, x i * (y.1 i, y.2 i))) = _
            rw [map_sum]
            rfl
        rw [heq, PoissonAutomorphyFiniteFourier.Construction.character_split]
        ring
    _ = _ := by
      simpa only [PoissonAutomorphyNormalizationData.fourier] using! integral_prod_mul (μ := volume) (ν := D.finiteMeasure)
        (fun y : ι → ℝ => f y * PoissonAutomorphyNormalizationData.standardRealCharacter (-(∑ i, (x i).1 * y i)))
        (fun y : ι → PoissonAutomorphyNormalizationData.AQf => φ y * D.finiteCharacter (-(∑ i, (x i).2 * y i)))

theorem adelic_fourier_pureTensor (f : PoissonAutomorphyNormalizationData.realSchwartz ι) (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (x : ι → PoissonAutomorphyNormalizationData.AQ) :
    PoissonAutomorphyNormalizationData.fourier D.character (PoissonAutomorphyNormalizationData.adelicMeasure D.finiteMeasure) (PoissonAutomorphyNormalizationData.pureTensor f φ) x =
      PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter volume f.val (fun i => (x i).1) *
        PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure φ.val (fun i => (x i).2) :=
  adelic_fourier_tensor_function D f.val φ.val x

end

end OAI.RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction
