import OAI.AlgebraicGeometry.PELModuli.IntegralModel.BasePointSectionMap

/-! # Span Generation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.SpanGeneration

noncomputable section

/-! A family spanning all global sections generates a line bundle
whenever global sections generate it. Vanishing at each point is the
kernel of the actual residue evaluation map over the original base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem section_family_covers_of_span
    {X S : Scheme.{u}} (f : X ⟶ S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    {ι : Type*} (v : ι → (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f L.sheaf).obj (op ⊤))
    (hv : Submodule.span Γ(S, ⊤) (Set.range v) = ⊤)
    (hgen : ∀ x : X, ∃ s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm (v i)) := by
  intro x
  by_contra hn
  push Not at hn
  let K := (BasePointSectionMap.basePointSectionMap f L.sheaf x).ker
  have hK : (⊤ : Submodule Γ(S, ⊤) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f L.sheaf).obj (op ⊤))) ≤ K := by
    rw [← hv]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (BasePointSectionMap.basePointSectionMap_eq_zero_iff f L x (v i)).mpr (hn i)
  obtain ⟨s, hs⟩ := hgen x
  let w : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f L.sheaf).obj (op ⊤) := AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf s
  have hz : BasePointSectionMap.basePointSectionMap f L.sheaf x w = 0 := hK (by trivial)
  have hn' := (BasePointSectionMap.basePointSectionMap_eq_zero_iff f L x w).mp hz
  have he : (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm w = s :=
    (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm_apply_apply s
  rw [he] at hn'
  exact hn' hs

theorem sectionHom_of_pullbackTopSection
    {X Y : Scheme.{u}} (a : Y ⟶ X) (M : X.Modules) (v : Γ(M, ⊤)) :
    (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M)).symm (CechPullbackSectionNormalization.pullbackTopSection a M v) =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection a ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm v) := by
  apply (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M)).injective
  rw [(AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj M)).apply_symm_apply]
  exact (congrArg (CechPullbackSectionNormalization.pullbackTopSection a M) ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).apply_symm_apply v).symm).trans
    (GlobalSectionPullbackValues.pullbackTopSection_hom_value a ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm v))

theorem pulled_section_family_covers_of_span
    {X Y S : Scheme.{u}} (a : Y ⟶ X) (f : Y ⟶ S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    {ι : Type*} (v : ι → Γ(L.sheaf, ⊤))
    (hv : Submodule.span Γ(S, ⊤) (Set.range (fun i =>
      (show (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f (L.pullback a).sheaf).obj (op ⊤) from
        CechPullbackSectionNormalization.pullbackTopSection a L.sheaf (v i)))) = ⊤)
    (hgen : ∀ y : Y, ∃ s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (L.pullback a).sheaf,
      y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    ∀ y : Y, ∃ i, y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection a ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm (v i))) := by
  have h := section_family_covers_of_span f (L.pullback a)
    (fun i => (show (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f (L.pullback a).sheaf).obj (op ⊤) from
      CechPullbackSectionNormalization.pullbackTopSection a L.sheaf (v i))) hv hgen
  intro y
  obtain ⟨i, hi⟩ := h y
  refine ⟨i, ?_⟩
  change y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing
    ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback a).obj L.sheaf)).symm
      (CechPullbackSectionNormalization.pullbackTopSection a L.sheaf (v i))) at hi
  simpa only [sectionHom_of_pullbackTopSection] using hi

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.SpanGeneration
