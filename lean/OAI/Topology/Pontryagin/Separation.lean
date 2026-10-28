import OAI.Topology.Pontryagin.Bochner

/-! # Separation -/

namespace OAI.Topology.Pontryagin.Separation.Constructions.CharacterExtension

noncomputable section

open Filter Function _root_.MeasureTheory Real Set _root_.Topology
open scoped Pointwise

section Bump
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

omit [μ.Regular] in
include μ in
theorem exists_positiveType_cc_eq_one (U : Set G) (hU : U ∈ nhds (1 : G)) :
    ∃ f : G → ℂ, PositiveType.IsPositiveType f ∧ Continuous f ∧ HasCompactSupport f ∧
      tsupport f ⊆ U ∧ f 1 = 1 := by
  -- a symmetric-ish neighborhood `V'` with `V' * V'⁻¹ ⊆ U`
  obtain ⟨V, hVopen, hV1, hVsub⟩ := exists_open_nhds_one_mul_subset hU
  set V' : Set G := V ∩ V⁻¹ with hV'def
  have hV'nhds : V' ∈ nhds (1 : G) :=
    Filter.inter_mem (hVopen.mem_nhds hV1)
      (inv_mem_nhds_one G (hVopen.mem_nhds hV1))
  obtain ⟨h, hhc, hhs, hh0, hhsupp, hhint⟩ := Translation.MeasureTheory.exists_normalized_bump μ V' hV'nhds
  set hC : G → ℂ := fun x => ((h x : ℝ) : ℂ) with hhCdef
  have hhCc : Continuous hC := Complex.continuous_ofReal.comp hhc
  have hhCs : HasCompactSupport hC := hhs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hhCsupp : tsupport hC ⊆ V' := by
    refine subset_trans (closure_mono fun x hx => ?_) hhsupp
    simp only [mem_support] at hx ⊢
    exact fun h0 => hx (by rw [hhCdef]; simp [h0])
  set e : G → ℂ := Convolution.MeasureTheory.mconv μ hC (Convolution.MeasureTheory.mstar hC) with hedef
  have hec : Continuous e := Convolution.Continuous.mconv (μ := μ) hhCc hhCs (Convolution.Continuous.mstar hhCc) (Convolution.HasCompactSupport.mstar hhCs)
  have hes : HasCompactSupport e := Convolution.HasCompactSupport.mconv (μ := μ) hhCs (Convolution.HasCompactSupport.mstar hhCs)
  have hpt : PositiveType.IsPositiveType e := PositiveType.isPositiveType_mconv_mstar μ hhCc hhCs
  -- support control
  have hesupp : tsupport e ⊆ U := by
    calc tsupport e ⊆ tsupport hC * tsupport (Convolution.MeasureTheory.mstar hC) :=
          Convolution.MeasureTheory.tsupport_mconv_subset μ hhCs (Convolution.HasCompactSupport.mstar hhCs)
      _ = tsupport hC * (tsupport hC)⁻¹ := by rw [Convolution.MeasureTheory.tsupport_mstar]
      _ ⊆ V' * V'⁻¹ := Set.mul_subset_mul hhCsupp (Set.inv_subset_inv.mpr hhCsupp)
      _ ⊆ V * V := by
          refine Set.mul_subset_mul (Set.inter_subset_left) ?_
          rw [hV'def, Set.inter_inv, inv_inv]
          exact Set.inter_subset_right
      _ ⊆ U := hVsub
  -- normalization
  have he1 : e 1 = ((∫ y, ‖hC y‖ ^ 2 ∂μ : ℝ) : ℂ) := Convolution.MeasureTheory.mconv_mstar_self_one μ hC
  have hr : 0 < ∫ y, ‖hC y‖ ^ 2 ∂μ := by
    have hsqeq : (fun y => ‖hC y‖ ^ 2) = fun y => h y ^ 2 := funext fun y => by
      show ‖((h y : ℝ) : ℂ)‖ ^ 2 = h y ^ 2
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hsqeq]
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, h x₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      rw [show h = fun _ => (0 : ℝ) from funext hcon] at hhint
      simp at hhint
    have hsqc : Continuous fun y => h y ^ 2 := by fun_prop
    have hsqs : HasCompactSupport fun y => h y ^ 2 := by
      refine hhs.mono fun y hy => ?_
      simp only [mem_support] at hy ⊢
      exact fun h0 => hy (by rw [h0]; ring)
    exact integral_pos_of_integrable_nonneg_nonzero (x := x₀) hsqc
      (hsqc.integrable_of_hasCompactSupport hsqs) (fun y => sq_nonneg _)
      (pow_ne_zero 2 hx₀)
  set r : ℝ := ∫ y, ‖hC y‖ ^ 2 ∂μ with hrdef
  refine ⟨r⁻¹ • e, hpt.smul_of_nonneg (inv_nonneg.mpr hr.le), hec.const_smul r⁻¹,
    hes.mono (support_const_smul_subset r⁻¹ e), ?_, ?_⟩
  · exact subset_trans (closure_mono (support_const_smul_subset r⁻¹ e)) hesupp
  · show r⁻¹ • e 1 = 1
    rw [he1, Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne',
      Complex.ofReal_one]

end Bump

/-- Continuous unitary characters distinguish every nonidentity point of an LCA group. -/
theorem eq_one_of_all_characters_one
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] {z : G}
    (hz : ∀ χ : PontryaginDual G, χ z = 1) : z = 1 := by
  classical
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace (PontryaginDual G) := borel (PontryaginDual G)
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  let μ := Measure.haarMeasure K₀
  by_contra hn
  obtain ⟨f, hpt, hfc, _hfs, hsupp, hf1⟩ :=
    exists_positiveType_cc_eq_one μ ({z}ᶜ) (compl_singleton_mem_nhds (Ne.symm hn))
  obtain ⟨σ, _hfin, _hreg, hrep⟩ := hpt.exists_bochner_measure μ hfc
  have hfz : f z = 1 := by
    calc f z = ∫ χ, (χ z : ℂ) ∂σ := hrep z
      _ = ∫ χ, (χ (1 : G) : ℂ) ∂σ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun χ =>
          congrArg (fun w : Circle => (w : ℂ)) ((hz χ).trans (map_one χ).symm)
      _ = f 1 := (hrep 1).symm
      _ = 1 := hf1
  have hzmem : z ∈ tsupport f := subset_closure (mem_support.mpr (hfz ▸ one_ne_zero))
  exact hsupp hzmem rfl

/-- Character separation with no measure or countability assumptions. -/
theorem characters_separate_points
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] (x y : G) (hxy : x ≠ y) :
    ∃ χ : PontryaginDual G, χ x ≠ χ y := by
  by_contra! h
  apply hxy
  apply div_eq_one.mp
  apply eq_one_of_all_characters_one
  intro χ
  rw [map_div, h χ]
  exact div_self' (χ y)

end

end OAI.Topology.Pontryagin.Separation.Constructions.CharacterExtension
