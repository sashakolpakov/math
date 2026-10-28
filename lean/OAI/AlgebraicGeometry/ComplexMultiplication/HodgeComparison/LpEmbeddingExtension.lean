import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpLocalization

/-! # Lp Embedding Extension -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpEmbeddingExtension.CM.Construction

noncomputable section

/-! Extension by zero along a genuine measurable embedding is an L2
isometry into the pushforward measure. -/

open _root_.MeasureTheory Set Filter

variable {X Y F 𝕜 : Type*} [NormedField 𝕜] [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (ν : Measure X) (φ : X → Y) (hφ : MeasurableEmbedding φ)

def measurableEmbeddingExtension (f : X → F) : Y → F := Function.extend φ f 0

include hφ

omit [NormedSpace 𝕜 F] [NormedField 𝕜] in
theorem measurableEmbeddingExtension_comp (f : X → F) :
    measurableEmbeddingExtension φ f ∘ φ = f :=
  Function.extend_comp hφ.injective f 0

omit [NormedSpace 𝕜 F] [NormedField 𝕜] in
theorem measurableEmbeddingExtension_memLp (f : Lp F 2 ν) :
    MemLp (measurableEmbeddingExtension φ f) 2 (Measure.map φ ν) := by
  change eLpNorm (measurableEmbeddingExtension φ f) 2 (Measure.map φ ν) < ⊤
  rw [hφ.eLpNorm_map_measure, measurableEmbeddingExtension_comp φ hφ]
  exact Lp.memLp f

def lpMeasurableEmbeddingExtension : Lp F 2 ν →ₗᵢ[𝕜] Lp F 2 (Measure.map φ ν) where
  toFun f := (measurableEmbeddingExtension_memLp ν φ hφ f).toLp _
  map_add' f g := by
    apply Lp.ext
    apply hφ.ae_map_iff.mpr
    have hp : MeasurePreserving φ ν (Measure.map φ ν) := ⟨hφ.measurable, rfl⟩
    filter_upwards [hp.quasiMeasurePreserving.ae (measurableEmbeddingExtension_memLp ν φ hφ (f + g)).coeFn_toLp,
      hp.quasiMeasurePreserving.ae (Lp.coeFn_add
        ((measurableEmbeddingExtension_memLp ν φ hφ f).toLp _)
        ((measurableEmbeddingExtension_memLp ν φ hφ g).toLp _)),
      hp.quasiMeasurePreserving.ae (measurableEmbeddingExtension_memLp ν φ hφ f).coeFn_toLp,
      hp.quasiMeasurePreserving.ae (measurableEmbeddingExtension_memLp ν φ hφ g).coeFn_toLp,
      Lp.coeFn_add f g] with x hl hr hf hg hfg
    rw [hl, hr]
    simp only [Pi.add_apply]
    rw [hf, hg]
    simp only [measurableEmbeddingExtension, hφ.injective.extend_apply]
    exact hfg
  map_smul' c f := by
    apply Lp.ext
    apply hφ.ae_map_iff.mpr
    have hp : MeasurePreserving φ ν (Measure.map φ ν) := ⟨hφ.measurable, rfl⟩
    filter_upwards [hp.quasiMeasurePreserving.ae (measurableEmbeddingExtension_memLp ν φ hφ (c • f)).coeFn_toLp,
      hp.quasiMeasurePreserving.ae (Lp.coeFn_smul c ((measurableEmbeddingExtension_memLp ν φ hφ f).toLp _)),
      hp.quasiMeasurePreserving.ae (measurableEmbeddingExtension_memLp ν φ hφ f).coeFn_toLp,
      Lp.coeFn_smul c f] with x hl hr hf hcf
    simp only [RingHom.id_apply]
    rw [hl, hr]
    simp only [Pi.smul_apply]
    rw [hf]
    simp only [measurableEmbeddingExtension, hφ.injective.extend_apply]
    exact hcf
  norm_map' f := by
    change ‖(measurableEmbeddingExtension_memLp ν φ hφ f).toLp _‖ = ‖f‖
    rw [Lp.norm_def, eLpNorm_congr_ae (measurableEmbeddingExtension_memLp ν φ hφ f).coeFn_toLp,
      hφ.eLpNorm_map_measure, measurableEmbeddingExtension_comp φ hφ, Lp.norm_def]

theorem lpMeasurableEmbeddingExtension_coe (f : Lp F 2 ν) :
    lpMeasurableEmbeddingExtension (𝕜 := 𝕜) ν φ hφ f =ᵐ[Measure.map φ ν] measurableEmbeddingExtension φ f :=
  (measurableEmbeddingExtension_memLp ν φ hφ f).coeFn_toLp

omit [NormedSpace 𝕜 F] [NormedField 𝕜] in
theorem measurableEmbeddingExtension_ae {f g : X → F} (hfg : f =ᵐ[ν] g) :
    measurableEmbeddingExtension φ f =ᵐ[Measure.map φ ν] measurableEmbeddingExtension φ g := by
  apply hφ.ae_map_iff.mpr
  filter_upwards [hfg] with x hx
  simpa only [measurableEmbeddingExtension, hφ.injective.extend_apply] using hx

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpEmbeddingExtension.CM.Construction
