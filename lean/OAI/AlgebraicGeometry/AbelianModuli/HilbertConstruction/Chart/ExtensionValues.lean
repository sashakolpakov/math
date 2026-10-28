import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ImageSectionMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.CoordinateValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.DegreeChartExtensions

/-! # Extension Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Convert the ratio condition for chart extensions into values of sections in
the explicit restriction sheaf. These identities are the input to comparison
of the local numerators on overlaps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {L M : Y.Modules}

/-- Restricting the image-open value of a local section gives its normalized
section value on the corresponding smaller open. -/
theorem Chart.ExtensionValues.pullbackSectionImageEquiv_restrict
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M) (V : X.Opens) :
    M.presheaf.map (f.opensFunctor.map V.leTop).op (SectionsOnOpenImages.pullbackSectionImageEquiv f M t) =
      (Open.ImageSectionMaps.normalizedPullbackSection f t).app V (1 : Γ(X, V)) :=
  Section.Gluing.moduleSectionHomEquiv_restrict (M.restrict f) (Open.ImageSectionMaps.normalizedPullbackSection f t) V

theorem Chart.ExtensionValues.normalizedPullbackSection_pullback_isIso (h : Z ⟶ X)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M)
    [ht : IsIso (Ample.LineBundles.pullbackSection h t)] :
    IsIso (Ample.LineBundles.pullbackSection h (Open.ImageSectionMaps.normalizedPullbackSection f t)) :=
  @Section.FrameTransport.pullbackSection_frameTransport_isIso Z X h _ _ (SectionsOnOpenImages.pullbackImageSourceIso f)
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm t ht

/-- The normalized denominator is a frame on the chart's part of `D(s)`. -/
theorem Chart.ExtensionValues.restrictPowerSection_local_isIso (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ) :
    IsIso (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι
      (Section.SectionRestriction.restrictSection f (TensorPower.Maps.tensorPowerSection s n))) := by
  let D := Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)
  have : IsIso (Ample.LineBundles.pullbackSection D.ι (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n))) :=
    Power.SectionTransport.iteratedPullback_power_isIso f n D.ι s
  have h := Chart.ExtensionValues.normalizedPullbackSection_pullback_isIso f D.ι (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n))
  exact (congrArg (fun t => IsIso (Ample.LineBundles.pullbackSection D.ι t))
    (Open.ImageSectionMaps.normalizedPullbackSection_pullback f (TensorPower.Maps.tensorPowerSection s n))).mp h

/-- Chart extension ratios remain the prescribed function after normalization
to the explicit restriction sheaf. -/
theorem Common.DegreeChartExtensions.ChartPowerExtends.normalized (s : Line.Bundles.structureModule Y ⟶ L)
    (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) (n : ℕ)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L n))
    (ht : Common.DegreeChartExtensions.ChartPowerExtends f s r n t) :
    letI := Chart.ExtensionValues.restrictPowerSection_local_isIso f s n
    Frame.Coordinates.frameCoordinate
      (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι
        (Section.SectionRestriction.restrictSection f (TensorPower.Maps.tensorPowerSection s n)))
      (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)).ι (Open.ImageSectionMaps.normalizedPullbackSection f t)) =
        (NonvanishingRestrictionMap.sectionNonvanishingMap f s).appTop r := by
  let D := Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)
  have h₀ : IsIso (Ample.LineBundles.pullbackSection D.ι (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n))) :=
    Power.SectionTransport.iteratedPullback_power_isIso f n D.ι s
  have h₁ : IsIso (Ample.LineBundles.pullbackSection D.ι
      (Open.ImageSectionMaps.normalizedPullbackSection f (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n)))) :=
    Chart.ExtensionValues.normalizedPullbackSection_pullback_isIso f D.ι _
  have h₂ : IsIso (Ample.LineBundles.pullbackSection D.ι (Section.SectionRestriction.restrictSection f (TensorPower.Maps.tensorPowerSection s n))) :=
    Chart.ExtensionValues.restrictPowerSection_local_isIso f s n
  have he := congrArg (Ample.LineBundles.pullbackSection D.ι) (Open.ImageSectionMaps.normalizedPullbackSection_pullback f (TensorPower.Maps.tensorPowerSection s n))
  have hc := @Frame.FrameRestriction.frameCoordinate_congr D.toScheme _ _ _
    (Ample.LineBundles.pullbackSection D.ι (Open.ImageSectionMaps.normalizedPullbackSection f t)) _ h₁ h₂ he rfl
  exact hc.symm.trans
    ((Open.ImageSectionMaps.normalizedPullbackSection_ratio f D.ι (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n)) t).trans ht)

/-- A normalized chart numerator has the ordinary section-value formula given
by its prescribed local ratio and the denominator power. -/
theorem Common.DegreeChartExtensions.ChartPowerExtends.normalized_value (s : Line.Bundles.structureModule Y ⟶ L)
    (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) (n : ℕ)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L n))
    (ht : Common.DegreeChartExtensions.ChartPowerExtends f s r n t) :
    let D := Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)
    (Open.ImageSectionMaps.normalizedPullbackSection f t).app (D.ι ''ᵁ ⊤) (1 : Γ(X, D.ι ''ᵁ ⊤)) =
      (D.ι.appIso ⊤).inv ((NonvanishingRestrictionMap.sectionNonvanishingMap f s).appTop r) •
        (Section.SectionRestriction.restrictSection f (TensorPower.Maps.tensorPowerSection s n)).app (D.ι ''ᵁ ⊤) (1 : Γ(X, D.ι ''ᵁ ⊤)) := by
  let D := Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)
  have : IsIso (Ample.LineBundles.pullbackSection D.ι (Section.SectionRestriction.restrictSection f (TensorPower.Maps.tensorPowerSection s n))) :=
    Chart.ExtensionValues.restrictPowerSection_local_isIso f s n
  have hv := Local.CoordinateValues.local_frameCoordinate_value D.ι (Section.SectionRestriction.restrictSection f (TensorPower.Maps.tensorPowerSection s n))
    (Open.ImageSectionMaps.normalizedPullbackSection f t)
  have hc := Common.DegreeChartExtensions.ChartPowerExtends.normalized f s r n t ht
  exact hv.trans (congrArg (fun c : Γ(D.toScheme, ⊤) => (D.ι.appIso ⊤).inv c •
    (Section.SectionRestriction.restrictSection f (TensorPower.Maps.tensorPowerSection s n)).app (D.ι ''ᵁ ⊤) (1 : Γ(X, D.ι ''ᵁ ⊤))) hc)

/-- The chart-extension condition gives an equality in the original power
sheaf on the image of the chart's part of `D(s)`. -/
theorem Common.DegreeChartExtensions.ChartPowerExtends.image_value (s : Line.Bundles.structureModule Y ⟶ L)
    (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) (n : ℕ)
    (t : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L n))
    (ht : Common.DegreeChartExtensions.ChartPowerExtends f s r n t) :
    let D := Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)
    let V := D.ι ''ᵁ ⊤
    (TensorPower.PowerSheaf.tensorPowerModule L n).presheaf.map (f.opensFunctor.map V.leTop).op
      (SectionsOnOpenImages.pullbackSectionImageEquiv f (TensorPower.PowerSheaf.tensorPowerModule L n) t) =
        (f.appIso V).inv ((D.ι.appIso ⊤).inv ((NonvanishingRestrictionMap.sectionNonvanishingMap f s).appTop r)) •
          (TensorPower.Maps.tensorPowerSection s n).app (f ''ᵁ V) (1 : Γ(Y, f ''ᵁ V)) := by
  let D := Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s)
  let V := D.ι ''ᵁ ⊤
  let c : Γ(X, V) := (D.ι.appIso ⊤).inv ((NonvanishingRestrictionMap.sectionNonvanishingMap f s).appTop r)
  have hv := Common.DegreeChartExtensions.ChartPowerExtends.normalized_value f s r n t ht
  change (Open.ImageSectionMaps.normalizedPullbackSection f t).app V (1 : Γ(X, V)) =
    (f.appIso V).inv c • (show Γ(TensorPower.PowerSheaf.tensorPowerModule L n, f ''ᵁ V) from
      (Section.SectionRestriction.restrictSection f (TensorPower.Maps.tensorPowerSection s n)).app V (1 : Γ(X, V))) at hv
  have hs := congrArg (fun z : Γ(TensorPower.PowerSheaf.tensorPowerModule L n, f ''ᵁ V) => (f.appIso V).inv c • z)
    (Section.SectionRestriction.restrictSection_app_one f (TensorPower.Maps.tensorPowerSection s n) V)
  exact (Chart.ExtensionValues.pullbackSectionImageEquiv_restrict f t V).trans (hv.trans hs)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
