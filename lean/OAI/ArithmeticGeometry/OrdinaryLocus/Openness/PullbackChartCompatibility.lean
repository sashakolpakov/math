import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleCharts
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackSectionCompatibility

/-! # Pullback Chart Compatibility -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackChartCompatibility.Construction

noncomputable section

/-! The chart comparison carries the canonical pullback of sections to the global pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

theorem modulePullbackSectionLE_top (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) (m : Γ(M, ⊤)) :
    PullbackSectionCompatibility.Construction.modulePullbackSectionLE f M ⊤ ⊤ h m = PullbackModuleSections.Construction.modulePullbackGlobalSection f M m := by
  change ((Scheme.Modules.pullback f).obj M).presheaf.map (𝟙 (.op ⊤))
    (PullbackModuleSections.Construction.modulePullbackGlobalSection f M m) = _
  simp

theorem moduleOpenPullbackSectionsMap_eq_sectionLE (U : Y.Opens) (m : Γ(M, U)) :
    OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap M U m =
      PullbackSectionCompatibility.Construction.modulePullbackSectionLE U.ι M U ⊤ U.ι_preimage_self.ge m := rfl

theorem modulePullbackOpenComparison_section (U : Y.Opens) (V : X.Opens)
    (hVU : V ≤ f ⁻¹ᵁ U) (m : Γ(M, U)) :
    (PullbackModuleCharts.Construction.modulePullbackOpenComparison f M U V hVU).hom.app ⊤
      (PullbackModuleSections.Construction.modulePullbackGlobalSection (f.resLE U V hVU) ((Scheme.Modules.pullback U.ι).obj M)
        (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap M U m)) =
      OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap ((Scheme.Modules.pullback f).obj M) V
        (PullbackSectionCompatibility.Construction.modulePullbackSectionLE f M U V hVU m) := by
  let a := (Scheme.Modules.pullbackComp (f.resLE U V hVU) U.ι).app M
  let b := (Scheme.Modules.pullbackCongr (f.resLE_comp_ι hVU)).app M
  let c := (Scheme.Modules.pullbackComp V.ι f).app M
  have h₁ := PullbackSectionCompatibility.Construction.modulePullbackSectionLE_comp (f.resLE U V hVU) U.ι M U ⊤ ⊤
    U.ι_preimage_self.ge (by simp) m
  have ht := modulePullbackSectionLE_top (f.resLE U V hVU) ((Scheme.Modules.pullback U.ι).obj M)
    (by simp) (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap M U m)
  have h₁ := (congrArg (a.hom.app ⊤) ht).symm.trans h₁
  have h₂ := PullbackSectionCompatibility.Construction.modulePullbackSectionLE_congr (f.resLE U V hVU ≫ U.ι) M
    (f.resLE_comp_ι hVU) U ⊤
    (show (⊤ : V.toScheme.Opens) ≤ (f.resLE U V hVU ≫ U.ι) ⁻¹ᵁ U from
      (show (⊤ : V.toScheme.Opens) ≤ (f.resLE U V hVU) ⁻¹ᵁ ⊤ from by simp).trans
        ((f.resLE U V hVU).preimage_mono U.ι_preimage_self.ge))
    (V.ι_preimage_self.ge.trans (V.ι.preimage_mono hVU)) m
  have h₃ := PullbackSectionCompatibility.Construction.modulePullbackSectionLE_comp V.ι f M U V ⊤ hVU V.ι_preimage_self.ge m
  have h : b.hom.app ⊤ (a.hom.app ⊤
      (PullbackModuleSections.Construction.modulePullbackGlobalSection (f.resLE U V hVU) ((Scheme.Modules.pullback U.ι).obj M)
        (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap M U m))) =
      c.hom.app ⊤ (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap ((Scheme.Modules.pullback f).obj M) V
        (PullbackSectionCompatibility.Construction.modulePullbackSectionLE f M U V hVU m)) := by
    exact (congrArg (b.hom.app ⊤) h₁).trans (h₂.trans h₃.symm)
  change c.inv.app ⊤ (b.hom.app ⊤ (a.hom.app ⊤
    (PullbackModuleSections.Construction.modulePullbackGlobalSection (f.resLE U V hVU) ((Scheme.Modules.pullback U.ι).obj M)
      (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap M U m)))) = _
  rw [h]
  exact congrArg (fun q : (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback f).obj M) ⟶
      (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback f).obj M) ↦
        q.app ⊤ (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap ((Scheme.Modules.pullback f).obj M) V
          (PullbackSectionCompatibility.Construction.modulePullbackSectionLE f M U V hVU m))) c.hom_inv_id

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackChartCompatibility.Construction
