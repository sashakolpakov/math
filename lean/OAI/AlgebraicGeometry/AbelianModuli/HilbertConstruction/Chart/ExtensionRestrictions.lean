import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.ExtensionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoordinatesOnOpenSubschemes
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingMapFunctions

/-! # Extension Restrictions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Chart numerators have one common section-value formula on the original
nonvanishing open. In particular, their restrictions agree wherever their
charts overlap inside that open.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {L : Y.Modules}

/-- The extension equation on the chart's actual nonvanishing open. -/
theorem Common.DegreeChartExtensions.ChartPowerExtends.value_on_open (s : Line.Bundles.structureModule Y ⟶ L)
    (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) (n : ℕ)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L n))
    (ht : Common.DegreeChartExtensions.ChartPowerExtends f s r n t) :
    let V := Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)
    (Open.ImageSectionMaps.normalizedPullbackSection f t).app V (1 : Γ(X, V)) =
      V.topIso.hom ((NonvanishingRestrictionMap.sectionNonvanishingMap f s).appTop r) •
        (Section.SectionRestriction.restrictSection f (TensorPower.Maps.tensorPowerSection s n)).app V (1 : Γ(X, V)) := by
  let V := Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)
  have : IsIso (Ample.LineBundles.pullbackSection V.ι (Section.SectionRestriction.restrictSection f (TensorPower.Maps.tensorPowerSection s n))) :=
    Chart.ExtensionValues.restrictPowerSection_local_isIso f s n
  exact (CoordinatesOnOpenSubschemes.local_frameCoordinate_value_on_open V (Section.SectionRestriction.restrictSection f (TensorPower.Maps.tensorPowerSection s n))
    (Open.ImageSectionMaps.normalizedPullbackSection f t)).trans
      (congrArg (fun c : Γ(V.toScheme, ⊤) => V.topIso.hom c •
        (Section.SectionRestriction.restrictSection f (TensorPower.Maps.tensorPowerSection s n)).app V (1 : Γ(X, V)))
          (Common.DegreeChartExtensions.ChartPowerExtends.normalized f s r n t ht))

/-- On its image inside `D(s)`, every chart numerator is the restriction of
the same coefficient times the denominator power. -/
theorem Common.DegreeChartExtensions.ChartPowerExtends.image_restriction (s : Line.Bundles.structureModule Y ⟶ L)
    (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) (n : ℕ)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L n))
    (ht : Common.DegreeChartExtensions.ChartPowerExtends f s r n t) :
    let V := Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)
    (TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map (f.opensFunctor.map V.leTop).op
      (SectionsOnOpenImages.pullbackSectionImageEquiv f (TensorPower.PowerSheaf.tensorPowerModule L n) t) =
        Y.presheaf.map (homOfLE (NonvanishingMapFunctions.sectionNonvanishing_image_le f s)).op
          ((Ample.LineBundles.sectionNonvanishing s).topIso.hom r) •
            (TensorPower.Maps.tensorPowerSection s n).app (f ''ᵁ V) (1 : Γ(Y, f ''ᵁ V)) := by
  let V := Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)
  let c : Γ(X, V) := V.topIso.hom ((NonvanishingRestrictionMap.sectionNonvanishingMap f s).appTop r)
  have hv := Common.DegreeChartExtensions.ChartPowerExtends.value_on_open f s r n t ht
  change (Open.ImageSectionMaps.normalizedPullbackSection f t).app V (1 : Γ(X, V)) =
    (f.appIso V).inv c • (show Γ(TensorPower.PowerSheaf.tensorPowerModule L n, f ''ᵁ V) from
      (Section.SectionRestriction.restrictSection f (TensorPower.Maps.tensorPowerSection s n)).app V (1 : Γ(X, V))) at hv
  exact (Chart.ExtensionValues.pullbackSectionImageEquiv_restrict f t V).trans (hv.trans
    (congrArg₂ (fun a : Γ(Y, f ''ᵁ V) => fun z : Γ(TensorPower.PowerSheaf.tensorPowerModule L n, f ''ᵁ V) => a • z)
      (NonvanishingMapFunctions.sectionNonvanishingMap_imageFunction f s r)
      (Section.SectionRestriction.restrictSection_app_one f (TensorPower.Maps.tensorPowerSection s n) V)))

/-- A section equation remains valid after restricting to a smaller open. -/
theorem Chart.ExtensionRestrictions.section_value_restrict {M : Y.Modules} {A B W : Y.Opens}
    (hWA : W ≤ A) (hWB : W ≤ B) (v : Γ(M, B)) (c : Γ(Y, A))
    (s : Line.Bundles.structureModule Y ⟶ M) (hAB : A ≤ B)
    (hv : M.presheaf.map (homOfLE hAB).op v = c • s.app A (1 : Γ(Y, A))) :
    M.presheaf.map (homOfLE hWB).op v =
      Y.presheaf.map (homOfLE hWA).op c • s.app W (1 : Γ(Y, W)) := by
  have hmap := congrArg (fun z : Γ(M, A) => M.presheaf.map (homOfLE hWA).op z) hv
  have hm := M.map_smul (homOfLE hWA) c (s.app A (1 : Γ(Y, A)))
  have hs := (M.unitHomEquiv s).property (homOfLE hWA).op
  have hc : M.presheaf.map (homOfLE hWA).op
      (M.presheaf.map (homOfLE hAB).op v) = M.presheaf.map (homOfLE hWB).op v :=
    (ConcreteCategory.congr_hom (M.presheaf.map_comp (homOfLE hAB).op (homOfLE hWA).op) v).symm
  exact hc.symm.trans (hmap.trans (hm.trans (congrArg (fun z =>
    Y.presheaf.map (homOfLE hWA).op c • z) hs)))

/-- The same formula holds on every smaller open contained in the chart and `D(s)`. -/
theorem Common.DegreeChartExtensions.ChartPowerExtends.restrict_to (s : Line.Bundles.structureModule Y ⟶ L)
    (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) (n : ℕ)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L n))
    (ht : Common.DegreeChartExtensions.ChartPowerExtends f s r n t) (W : Y.Opens)
    (hWf : W ≤ f ''ᵁ ⊤) (hWD : W ≤ Ample.LineBundles.sectionNonvanishing s) :
    (TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map (homOfLE hWf).op
      (SectionsOnOpenImages.pullbackSectionImageEquiv f (TensorPower.PowerSheaf.tensorPowerModule L n) t) =
        Y.presheaf.map (homOfLE hWD).op ((Ample.LineBundles.sectionNonvanishing s).topIso.hom r) •
          (TensorPower.Maps.tensorPowerSection s n).app W (1 : Γ(Y, W)) := by
  let V := Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)
  have hWV : W ≤ f ''ᵁ V := by
    dsimp [V]
    rw [Section.Nonvanishing.sectionNonvanishing_pullback, Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact le_inf (hWf.trans (by simp)) hWD
  have hv := Chart.ExtensionRestrictions.section_value_restrict hWV hWf
    (SectionsOnOpenImages.pullbackSectionImageEquiv f (TensorPower.PowerSheaf.tensorPowerModule L n) t)
    (Y.presheaf.map (homOfLE (NonvanishingMapFunctions.sectionNonvanishing_image_le f s)).op
      ((Ample.LineBundles.sectionNonvanishing s).topIso.hom r))
    (TensorPower.Maps.tensorPowerSection s n) (f.opensFunctor.map V.leTop).le
    (Common.DegreeChartExtensions.ChartPowerExtends.image_restriction f s r n t ht)
  have hc : Y.presheaf.map (homOfLE hWV).op
      (Y.presheaf.map (homOfLE (NonvanishingMapFunctions.sectionNonvanishing_image_le f s)).op
        ((Ample.LineBundles.sectionNonvanishing s).topIso.hom r)) =
      Y.presheaf.map (homOfLE hWD).op ((Ample.LineBundles.sectionNonvanishing s).topIso.hom r) :=
    (ConcreteCategory.congr_hom (Y.presheaf.map_comp
      (homOfLE (NonvanishingMapFunctions.sectionNonvanishing_image_le f s)).op (homOfLE hWV).op) _).symm
  exact hv.trans (congrArg (fun c : Γ(Y, W) => c •
    (TensorPower.Maps.tensorPowerSection s n).app W (1 : Γ(Y, W))) hc)

/-- Two chart numerators agree on every common open inside `D(s)`. -/
theorem Common.DegreeChartExtensions.ChartPowerExtends.agree_on {Z : Scheme.{u}} (g : Z ⟶ Y) [IsOpenImmersion g]
    (s : Line.Bundles.structureModule Y ⟶ L) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) (n : ℕ)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L n))
    (t' : Line.Bundles.structureModule Z ⟶ (Scheme.Modules.pullback g).obj (TensorPower.PowerSheaf.tensorPowerModule L n))
    (ht : Common.DegreeChartExtensions.ChartPowerExtends f s r n t) (ht' : Common.DegreeChartExtensions.ChartPowerExtends g s r n t')
    (W : Y.Opens) (hWf : W ≤ f ''ᵁ ⊤) (hWg : W ≤ g ''ᵁ ⊤)
    (hWD : W ≤ Ample.LineBundles.sectionNonvanishing s) :
    (TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map (homOfLE hWf).op
      (SectionsOnOpenImages.pullbackSectionImageEquiv f (TensorPower.PowerSheaf.tensorPowerModule L n) t) =
    (TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map (homOfLE hWg).op
      (SectionsOnOpenImages.pullbackSectionImageEquiv g (TensorPower.PowerSheaf.tensorPowerModule L n) t') :=
  (Common.DegreeChartExtensions.ChartPowerExtends.restrict_to f s r n t ht W hWf hWD).trans
    (Common.DegreeChartExtensions.ChartPowerExtends.restrict_to g s r n t' ht' W hWg hWD).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
