import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.SectionDetection

/-! # Global Section Generation -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionGeneration

noncomputable section

/-! Global sections generate a module sheaf exactly when they detect maps
out of it. Generation means the actual section-evaluation map is an epimorphism. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u v

def SectionsDetectMaps {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ (N : X.Modules) (a : M ⟶ N), a.app ⊤ = 0 → a = 0

private theorem sectionMap_comp_zero {X : Scheme.{u}} {L M N : X.Modules}
    (f : L ⟶ M) (a : M ⟶ N) (ha : a.app ⊤ = 0) : (f ≫ a).app ⊤ = 0 := by
  ext x
  change a.app ⊤ (f.app ⊤ x) = 0
  rw [ha]
  rfl

theorem _root_.OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.SectionDetection.Construction.HasFrameSections.sectionsDetectMaps {X : Scheme.{u}} {M : X.Modules}
    (h : Frame.SectionDetection.Construction.HasFrameSections M) : Construction.SectionsDetectMaps M :=
  fun _ a ha => h.hom_eq_zero a ha

theorem SectionsDetectMaps.of_epi {X : Scheme.{u}} {M N : X.Modules}
    (h : SectionsDetectMaps M) (f : M ⟶ N) [Epi f] : SectionsDetectMaps N := by
  intro P a ha
  apply (cancel_epi f).mp
  rw [comp_zero]
  exact h P (f ≫ a) (sectionMap_comp_zero f a ha)

theorem SectionsDetectMaps.coproduct {X : Scheme.{u}} {ι : Type v}
    (M : ι → X.Modules) [HasCoproduct M] (h : ∀ i, SectionsDetectMaps (M i)) :
    SectionsDetectMaps (∐ M) := by
  intro N a ha
  apply Sigma.hom_ext
  intro i
  rw [comp_zero]
  exact h i N (Sigma.ι M i ≫ a) (sectionMap_comp_zero _ a ha)

def globalSectionEvaluation {X : Scheme.{u}} (M : X.Modules) :
    (∐ fun _ : Γ(M, ⊤) => AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ⟶ M :=
  Sigma.desc fun s => (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm s

theorem SectionsDetectMaps.evaluation_epi {X : Scheme.{u}} {M : X.Modules}
    (hM : SectionsDetectMaps M) : Epi (globalSectionEvaluation M) := by
  apply Preadditive.epi_of_cancel_zero
  intro N a ha
  apply hM N a
  ext s
  have hs : (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm s ≫ a = 0 := by
    have hh := congrArg
      (fun q => Sigma.ι (fun _ : Γ(M, ⊤) => AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) s ≫ q) ha
    simpa only [globalSectionEvaluation, Sigma.ι_comp_desc_assoc, comp_zero] using hh
  have hh := congrArg (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv N) hs
  change a.app ⊤ (((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm s).app ⊤ (1 : Γ(X, ⊤))) = 0 at hh
  have he : ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm s).app ⊤ (1 : Γ(X, ⊤)) = s :=
    (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).apply_symm_apply s
  rw [he] at hh
  exact hh

theorem sectionsDetectMaps_of_evaluation_epi {X : Scheme.{u}} (M : X.Modules)
    [Epi (globalSectionEvaluation M)] : SectionsDetectMaps M := by
  exact (SectionsDetectMaps.coproduct (fun _ : Γ(M, ⊤) => AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (fun _ => (Frame.SectionDetection.Construction.hasFrameSections_structure X).sectionsDetectMaps)).of_epi
      (globalSectionEvaluation M)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionGeneration
