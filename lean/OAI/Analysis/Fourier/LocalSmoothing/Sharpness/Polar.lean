import OAI.Analysis.Fourier.Restriction.Polar

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Metric _root_.MeasureTheory
open scoped ENNReal

/-- Polar integration for the actual surface measure used in the sphere
Fourier asymptotic, with the radius integrated last. -/
theorem integral_polar_sphereMeasure {n : ℕ} (hn : 1 ≤ n)
    {F : Space n → ℂ} (hFc : Continuous F) (hF : Integrable F) :
    (∫ x, F x) = ∫ t in Ioi (0 : ℝ),
      (t ^ (n-1)) • (∫ ω, F (t • ω) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  let : NeZero n := ⟨by omega⟩
  let E := Space n
  let H := homeomorphUnitSphereProd E
  let G : sphere (0:E) 1 × Ioi (0:ℝ) → ℂ := fun z => F (z.2.1 • z.1.1)
  have hp := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd
  have hp' : MeasurePreserving H (volume.comap Subtype.val)
      (volume.toSphere.prod (Measure.volumeIoiPow (n-1))) := by
    simpa only [H,E,Space,finrank_euclideanSpace,Fintype.card_fin] using hp
  have hsub : Integrable (fun x : ({(0:E)}ᶜ : Set E) => F x)
      (volume.comap Subtype.val) := by
    apply (integrableOn_iff_comap_subtypeVal (by measurability)).mp
    exact hF.integrableOn
  have hG : Integrable G (volume.toSphere.prod (Measure.volumeIoiPow (n-1))) := by
    change Integrable (fun z => F (H.symm z)) _
    apply (hp'.integrable_comp_emb H.measurableEmbedding).mp
    simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using hsub
  calc
    (∫ x, F x) = ∫ x : ({(0:E)}ᶜ : Set E), F x ∂volume.comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl F,
        restrict_compl_singleton]
    _ = ∫ z, G z ∂volume.toSphere.prod (Measure.volumeIoiPow (n-1)) := by
      simpa only [G,H,E,Space,finrank_euclideanSpace,Fintype.card_fin,
        Function.comp_apply,homeomorphUnitSphereProd_symm_apply_coe,
        Homeomorph.symm_apply_apply] using
        hp.integral_comp H.measurableEmbedding (fun z => F (H.symm z))
    _ = ∫ t : Ioi (0:ℝ), (∫ ω : sphere (0:E) 1, F (t.1 • ω.1) ∂volume.toSphere)
        ∂Measure.volumeIoiPow (n-1) := integral_prod_symm G hG
    _ = ∫ t in Ioi (0:ℝ), (t^(n-1)) •
        (∫ ω : sphere (0:E) 1, F (t • ω.1) ∂volume.toSphere) := by
      simp only [Measure.volumeIoiPow,ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul]
      · rw [integral_subtype_comap measurableSet_Ioi
          (fun t : ℝ => Real.toNNReal (t^(n-1)) •
            (∫ ω : sphere (0:E) 1, F (t • ω.1) ∂volume.toSphere))]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [NNReal.smul_def,Real.coe_toNNReal _ (pow_nonneg ht.le _)]
      · exact (measurable_subtype_coe.pow_const _).real_toNNReal
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      congr 1
      rw [OAI.Analysis.Fourier.Restriction.sphereMeasure,integral_map]
      · exact measurable_subtype_coe.aemeasurable
      · have hm : Continuous (fun ω : Space n => F (t • ω)) := by fun_prop
        exact hm.aestronglyMeasurable

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
