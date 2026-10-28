import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.NumeratorGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.FromSectionValue

/-! # Section Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Extend a regular function on a section's nonvanishing open to a numerator in
a positive tensor power of a line bundle on a quasi-compact separated scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v

variable {Y : Scheme.{u}} {L : Y.Modules}

/-- Local extension ratios determine one section-value equation on all of `D(s)`. -/
theorem Global.SectionExtension.chart_extensions_global_value {ι : Type v} (U : ι → Y.Opens)
    (cover : ∀ y : Y, ∃ i, y ∈ U i)
    (s : Line.Bundles.structureModule Y ⟶ L) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) (n : ℕ)
    (a : Line.Bundles.structureModule Y ⟶ TensorPower.PowerSheaf.tensorPowerModule L n)
    (ha : ∀ i, Common.DegreeChartExtensions.ChartPowerExtends (U i).ι s r n (Ample.LineBundles.pullbackSection (U i).ι a)) :
    a.app (Ample.LineBundles.sectionNonvanishing s) (1 : Γ(Y, Ample.LineBundles.sectionNonvanishing s)) =
      (Ample.LineBundles.sectionNonvanishing s).topIso.hom r •
        (TensorPower.Maps.tensorPowerSection s n).app (Ample.LineBundles.sectionNonvanishing s) (1 : Γ(Y, Ample.LineBundles.sectionNonvanishing s)) := by
  let D := Ample.LineBundles.sectionNonvanishing s
  let P := TensorPower.PowerSheaf.tensorPowerModule L n
  let W (i : ι) := ((U i).ι ''ᵁ ⊤) ⊓ D
  let F : TopCat.Sheaf AddCommGrpCat Y := ⟨P.presheaf, P.isSheaf⟩
  have hcover : D ≤ iSup W := by
    intro y hy
    obtain ⟨i, hi⟩ := cover y
    exact Opens.mem_iSup.mpr ⟨i,
      (congrArg (fun B : Y.Opens => y ∈ B) (U i).ι_image_top).mpr hi, hy⟩
  apply F.eq_of_locally_eq' W D (fun _ => homOfLE inf_le_right) hcover
  intro i
  have he := Common.DegreeChartExtensions.ChartPowerExtends.restrict_to (U i).ι s r n (Ample.LineBundles.pullbackSection (U i).ι a)
    (ha i) (W i) inf_le_left inf_le_right
  have hl : P.presheaf.map (homOfLE (show W i ≤ (U i).ι ''ᵁ ⊤ from inf_le_left)).op
      (SectionsOnOpenImages.pullbackSectionImageEquiv (U i).ι P (Ample.LineBundles.pullbackSection (U i).ι a)) =
        a.app (W i) (1 : Γ(Y, W i)) :=
    (congrArg (fun z : Γ(P, (U i).ι ''ᵁ ⊤) =>
      P.presheaf.map (homOfLE (show W i ≤ (U i).ι ''ᵁ ⊤ from inf_le_left)).op z)
        (SectionsOnOpenImages.pullbackSectionImageEquiv_pullback (U i).ι P a)).trans
          ((P.unitHomEquiv a).property (homOfLE (show W i ≤ (U i).ι ''ᵁ ⊤ from inf_le_left)).op)
  have hnum := (P.unitHomEquiv a).property (homOfLE (show W i ≤ D from inf_le_right)).op
  have hden := (P.unitHomEquiv (TensorPower.Maps.tensorPowerSection s n)).property
    (homOfLE (show W i ≤ D from inf_le_right)).op
  have hrhs := (P.map_smul (homOfLE (show W i ≤ D from inf_le_right)) (D.topIso.hom r)
    ((TensorPower.Maps.tensorPowerSection s n).app D (1 : Γ(Y, D)))).trans
      (congrArg (fun z : Γ(P, W i) =>
        Y.presheaf.map (homOfLE (show W i ≤ D from inf_le_right)).op (D.topIso.hom r) • z) hden)
  exact hnum.trans (hl.symm.trans (he.trans hrhs.symm))

/-- A global numerator represents the prescribed function after division by `s^n` on `D(s)`. -/
def Global.SectionExtension.PowerExtends (s : Line.Bundles.structureModule Y ⟶ L)
    (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) (n : ℕ)
    (a : Line.Bundles.structureModule Y ⟶ TensorPower.PowerSheaf.tensorPowerModule L n) : Prop :=
  letI := Power.Nonvanishing.tensorPowerSection_pullback_isIso (Ample.LineBundles.sectionNonvanishing s).ι s n
  Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι (TensorPower.Maps.tensorPowerSection s n))
    (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι a) = r

/-- Section extension for a line bundle on a quasi-compact separated scheme. -/
theorem Line.Bundles.LineBundle.section_extension (L : Line.Bundles.LineBundle Y) [CompactSpace Y] [Y.IsSeparated]
    (s : Line.Bundles.structureModule Y ⟶ L.sheaf) (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) :
    ∃ (n : ℕ) (_ : 0 < n) (a : Line.Bundles.structureModule Y ⟶ TensorPower.PowerSheaf.tensorPowerModule L.sheaf n),
      Global.SectionExtension.PowerExtends s r n a := by
  obtain ⟨n, hn, a, k, U, cover, ha⟩ := L.exists_global_chart_extension s r
  have : IsIso (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι (TensorPower.Maps.tensorPowerSection s n)) :=
    Power.Nonvanishing.tensorPowerSection_pullback_isIso (Ample.LineBundles.sectionNonvanishing s).ι s n
  exact ⟨n, hn, a, Coordinate.FromSectionValue.local_frameCoordinate_eq_of_value_on_open (Ample.LineBundles.sectionNonvanishing s)
    (TensorPower.Maps.tensorPowerSection s n) a r (Global.SectionExtension.chart_extensions_global_value U cover s r n a ha)⟩

/-- Increasing the numerator's degree by powers of `s` preserves the represented function. -/
theorem Global.SectionExtension.PowerExtends.transition (s : Line.Bundles.structureModule Y ⟶ L)
    (r : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) (n m : ℕ)
    (a : Line.Bundles.structureModule Y ⟶ TensorPower.PowerSheaf.tensorPowerModule L n) (ha : Global.SectionExtension.PowerExtends s r n a) :
    Global.SectionExtension.PowerExtends s r (n + m) (a ≫ Power.SectionTransitions.powerSectionTransition s n m) := by
  have : IsIso (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι (TensorPower.Maps.tensorPowerSection s n)) :=
    Power.Nonvanishing.tensorPowerSection_pullback_isIso (Ample.LineBundles.sectionNonvanishing s).ι s n
  have : IsIso (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι (TensorPower.Maps.tensorPowerSection s (n + m))) :=
    Power.Nonvanishing.tensorPowerSection_pullback_isIso (Ample.LineBundles.sectionNonvanishing s).ι s (n + m)
  exact (Power.SectionTransitions.frameCoordinate_pullback_postcomp (Ample.LineBundles.sectionNonvanishing s).ι (TensorPower.Maps.tensorPowerSection s n)
    (TensorPower.Maps.tensorPowerSection s (n + m)) (Power.SectionTransitions.powerSectionTransition s n m)
    (Power.SectionTransitions.tensorPowerSection_transition s n m) a).trans ha

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
