import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackChartCompatibility

/-! # Canonical Chart Sections -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CanonicalChartSections.Construction

noncomputable section

/-! Canonical section coordinates associated to an actual line-bundle chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {X Y : Scheme.{u}} {M : Y.Modules} (U : Y.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ LineBundle.Construction.structureSheafModule U.toScheme)

theorem openInclusion_appLE_eq_topIso_inv : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE]
  rfl

def moduleChartSectionsAddEquiv : Γ(M, U) ≃+ Γ(Y, U) :=
  (OpenPullbackSections.Construction.moduleOpenPullbackSectionsEquiv M U).trans
    ((PullbackTensorNaturality.Construction.moduleGlobalSectionsIso e).toAddEquiv.trans U.topIso.commRingCatIsoToRingEquiv.toAddEquiv)

theorem moduleChartSectionsAddEquiv_apply (m : Γ(M, U)) :
    moduleChartSectionsAddEquiv U e m = U.topIso.hom (e.hom.app ⊤ (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap M U m)) :=
  rfl

theorem moduleChartSectionsAddEquiv_smul (r : Γ(Y, U)) (m : Γ(M, U)) :
    moduleChartSectionsAddEquiv U e (r • m) = r * moduleChartSectionsAddEquiv U e m := by
  rw [moduleChartSectionsAddEquiv_apply, OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap_smul,
    e.hom.app_smul, openInclusion_appLE_eq_topIso_inv]
  let z : Γ(U, ⊤) := e.hom.app ⊤ (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap M U m)
  change U.topIso.hom (U.topIso.inv r * z) = _
  rw [U.topIso.hom.hom.map_mul]
  exact congrArg (fun a : Γ(Y, U) ↦ a * moduleChartSectionsAddEquiv U e m)
    (congrArg (fun q : Γ(Y, U) ⟶ Γ(Y, U) ↦ q r) U.topIso.inv_hom_id)

def moduleChartSectionsEquiv :
    Γ(M, U) ≃ₗ[Γ(Y, U)] Γ(Y, U) where
  __ := moduleChartSectionsAddEquiv U e
  map_smul' r m := moduleChartSectionsAddEquiv_smul U e r m

theorem pullbackLineBundleChart_section (f : X ⟶ Y) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U)
    (m : Γ(M, U)) :
    (PullbackModuleCharts.Construction.pullbackLineBundleChart f M U V hVU e).hom.app ⊤
      (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap ((Scheme.Modules.pullback f).obj M) V
        (PullbackSectionCompatibility.Construction.modulePullbackSectionLE f M U V hVU m)) =
      (f.resLE U V hVU).appTop (e.hom.app ⊤ (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap M U m)) := by
  let q := PullbackModuleCharts.Construction.modulePullbackOpenComparison f M U V hVU
  let s := PullbackModuleSections.Construction.modulePullbackGlobalSection (f.resLE U V hVU) ((Scheme.Modules.pullback U.ι).obj M)
    (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap M U m)
  have h := PullbackChartCompatibility.Construction.modulePullbackOpenComparison_section f M U V hVU m
  have hc : q.inv.app ⊤ (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap ((Scheme.Modules.pullback f).obj M) V
      (PullbackSectionCompatibility.Construction.modulePullbackSectionLE f M U V hVU m)) = s := by
    rw [← h]
    exact congrArg (fun t : (Scheme.Modules.pullback (f.resLE U V hVU)).obj
        ((Scheme.Modules.pullback U.ι).obj M) ⟶
        (Scheme.Modules.pullback (f.resLE U V hVU)).obj ((Scheme.Modules.pullback U.ι).obj M) ↦
          t.app ⊤ s) q.hom_inv_id
  change (LineBundle.Construction.pullbackStructureSheafIso (f.resLE U V hVU)).hom.app ⊤
    (((Scheme.Modules.pullback (f.resLE U V hVU)).map e.hom).app ⊤
      (q.inv.app ⊤ (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap ((Scheme.Modules.pullback f).obj M) V
        (PullbackSectionCompatibility.Construction.modulePullbackSectionLE f M U V hVU m)))) = _
  rw [hc]
  change (LineBundle.Construction.pullbackStructureSheafIso (f.resLE U V hVU)).hom.app ⊤
    (((Scheme.Modules.pullback (f.resLE U V hVU)).map e.hom).app ⊤
      (PullbackModuleSections.Construction.modulePullbackGlobalSection (f.resLE U V hVU) ((Scheme.Modules.pullback U.ι).obj M)
        (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap M U m))) = _
  rw [PullbackModuleSections.Construction.modulePullbackGlobalSection_naturality]
  exact PullbackModuleSections.Construction.modulePullbackGlobalSection_unit (f.resLE U V hVU)
    (e.hom.app ⊤ (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap M U m))

theorem moduleChartSectionsEquiv_pullback (f : X ⟶ Y) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U)
    (m : Γ(M, U)) :
    moduleChartSectionsEquiv V (PullbackModuleCharts.Construction.pullbackLineBundleChart f M U V hVU e)
      (PullbackSectionCompatibility.Construction.modulePullbackSectionLE f M U V hVU m) = f.appLE U V hVU (moduleChartSectionsEquiv U e m) := by
  change V.topIso.hom ((PullbackModuleCharts.Construction.pullbackLineBundleChart f M U V hVU e).hom.app ⊤
    (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap ((Scheme.Modules.pullback f).obj M) V
      (PullbackSectionCompatibility.Construction.modulePullbackSectionLE f M U V hVU m))) = _
  rw [pullbackLineBundleChart_section]
  have h := (arrowResLEAppIso f U V hVU).hom.w
  exact (congrArg (fun q : Γ(U, ⊤) ⟶ Γ(X, V) ↦
    q (e.hom.app ⊤ (OpenPullbackSections.Construction.moduleOpenPullbackSectionsMap M U m))) h).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CanonicalChartSections.Construction
