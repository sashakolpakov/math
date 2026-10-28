import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FlatGlobalBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.GlobalSections
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.SectionGenerators
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.SpanGeneration

/-! # Flat Section Generation Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatSectionGenerationDescent

noncomputable section

/-! Global generation descends through a surjective flat coefficient
base change, using finitely many actual sections of the original family. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

theorem properFlat_exists_generating_sections_of_flat_baseChange
    {X Y S T : Scheme.{0}} [IsAffine S] [IsAffine T] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (a : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback a ρ f g)
    (hg : g.appTop.hom.Flat) (ha : Function.Surjective a)
    (hgen : ∀ y : Y, ∃ s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (L.pullback a).sheaf,
      y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    ∃ (n : ℕ) (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf)),
      ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) := by
  have : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  have : L.sheaf.IsFiniteType := by
    let : L.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
    obtain ⟨p, hp⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.sheaf
    refine { exists_localGeneratorsData := ⟨p.localGeneratorsData, ?_⟩ }
    constructor
    intro i
    exact (hp.isFinite_presentation i).isFiniteType_generators
  have : Module.Finite Γ(S, ⊤) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f L.sheaf).obj (op ⊤)) :=
    Proper.GlobalSections.proper_coherent_baseModuleTop_finite f L.sheaf
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := Γ(S, ⊤))
    (M := (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f L.sheaf).obj (op ⊤))
  obtain ⟨b, hb, hbone⟩ := Proper.FlatGlobalBaseChange.properFlat_exists_surjective_section_map_of_flat f L a ρ g hp hg
  have hspan := Scalar.SectionGenerators.scalar_images_span_of_surjective g.appTop.hom _ _ b hb v hv
  simp only [hbone] at hspan
  let s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf) :=
    Fin.lastCases 0 (fun i => (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm (v i))
  refine ⟨n, s, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := ha x
  obtain ⟨i, hi⟩ := Section.SpanGeneration.pulled_section_family_covers_of_span a ρ L v hspan hgen y
  refine ⟨i.castSucc, ?_⟩
  rw [AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange _ L] at hi
  change a y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm (v i)) at hi
  simpa only [s, Fin.lastCases_castSucc] using hi

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatSectionGenerationDescent
