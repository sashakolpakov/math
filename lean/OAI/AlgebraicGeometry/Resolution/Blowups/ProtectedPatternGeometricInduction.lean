import OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedPatternChartStep
import OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedPatternHeadDichotomy
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledIdealProtectedOpen
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.StrictImageOpenRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Projectivity
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.SchemeImage

/-! # Protected Pattern Geometric Induction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Finite actual control programs produce a smooth strict image while preserving the protected open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_smooth_protected_image
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 X f J Y g K) (hK : K = ⊤) :
    ∀ [IsIntegral X] [IsLocallyNoetherian X] (_A : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f)
      (O : X.Opens) (Z : Scheme) [IsIntegral Z] [NoetherianSpace Z]
      (i : Z ⟶ O.toScheme) [IsClosedImmersion i],
      J.comap O.ι = i.ker → ProtectedPatternChart.Construction.ProtectedPatternProgramCover P O →
      ∃ (V : Scheme) (π : V ⟶ X),
        Nonempty (Foundations.Scheme.SmoothProjective.ProjectivePresentation V (π ≫ f)) ∧ IsProper π ∧ IsIso (π ∣_ O) ∧
        ∃ q : Z ⟶ V, q ≫ π = i ≫ O.ι ∧ Smooth (q.imageι ≫ (π ≫ f)) := by
  induction P with
  | @stop X f hf J =>
      intro hX hNX A O Z hZ hNZ i hi hJ _
      have ht : i.ker = ⊤ := hJ.symm.trans (by rw [hK, Scheme.IdealSheafData.comap_top])
      let : IsEmpty Z := i.ker_eq_top_iff_isEmpty.mp ht
      exact isEmptyElim (Classical.choice (inferInstance : Nonempty Z))
  | @blowup X hX hNX f J C hC hb hp hs hbl Y g K tail ih =>
      intro _ _ A O Z hZ hNZ i hi hJ cover
      let : IsIntegral (J.comap O.ι).subscheme := by
        rw [hJ]
        exact Integral.SchemeImage.Construction.scheme_image_isIntegral i
      rcases ProtectedPatternHeadDichotomy.Construction.protected_pattern_head_center_dichotomy C hC hp hs hbl tail O cover with hwhole | hempty
      · let : Smooth (C.subschemeι ≫ f) := hs
        have hsm := Blowups.Smooth.StrictImageOpenRestriction.Construction.schemeImage_smooth_of_closed_open_restriction i O.ι f C (hwhole.trans hJ)
        refine ⟨X, 𝟙 X, ⟨?_⟩, inferInstance, inferInstance, i ≫ O.ι, by simp, ?_⟩
        · simpa only [Category.id_comp] using A
        · simpa only [Category.id_comp] using hsm
      · let π := GlobalBlowup.Data.Construction.globalBlowupToBase C hC
        let O' := π ⁻¹ᵁ O
        let ρ := π ∣_ O
        let : IsIso ρ := ControlledIdealProtectedOpen.Construction.globalBlowup_isIso_on_open_of_comap_top C hC O hempty
        let i' := i ≫ inv ρ
        have hJ' : (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C J hC 1).comap O'.ι = i'.ker := by
          rw [ControlledIdealProtectedOpen.Construction.globalBlowupControlledIdeal_restrict_of_comap_top C J hC 1 O hempty, hJ]
          have he := Locally.ClosedImageRestriction.Construction.kernel_comap_of_comp_open i' ρ
          simpa only [i', Category.assoc, IsIso.inv_hom_id, Category.comp_id] using he
        obtain ⟨cover'⟩ := ProtectedPatternChartStep.Construction.exists_protected_pattern_cover_after_empty_step C hC hp hs hbl tail O hempty cover
        obtain ⟨V, p, ⟨Q⟩, hpV, hpO, q, hq, hsm⟩ :=
          ih hK (GlobalBlowup.Projectivity.Construction.globalBlowupProjectivePresentation A C hC) O' Z i' hJ' cover'
        let : IsProper p := hpV
        let : IsIso (p ∣_ O') := hpO
        refine ⟨V, p ≫ π, ⟨?_⟩, inferInstance, ?_, q, ?_, ?_⟩
        · simpa only [Category.assoc] using Q
        · exact (morphismRestrict_comp p π O).symm ▸
            (inferInstance : IsIso ((p ∣_ π ⁻¹ᵁ O) ≫ (π ∣_ O)))
        · rw [← Category.assoc, hq]
          change (i ≫ inv ρ) ≫ O'.ι ≫ π = i ≫ O.ι
          rw [← morphismRestrict_ι, Category.assoc, IsIso.inv_hom_id_assoc]
        · simpa only [Category.assoc] using hsm

end

end OAI.AlgebraicGeometry.Resolution.Blowups
