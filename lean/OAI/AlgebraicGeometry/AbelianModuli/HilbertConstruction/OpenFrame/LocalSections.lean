import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModuleSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GeneratorNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionMapValues

/-! # Local Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalSections

noncomputable section

/-! The constructed frame sheaf has canonical sections on each chart, with explicit values on every smaller open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

theorem openInclusionImage_le (V : X.Opens) (W : V.toScheme.Opens) : V.ι ''ᵁ W ≤ V := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

def openFrameLocalSection (k : ι) :
    Line.Bundles.structureModule (U k).toScheme ⟶ (ModuleSheaf.openFrameModuleSheaf D).restrict (U k).ι :=
  (Global.Sections.moduleSectionHomEquiv ((ModuleSheaf.openFrameModuleSheaf D).restrict (U k).ι)).symm
    (SectionGenerators.openFrameGenerator D ((U k).ι ''ᵁ ⊤) k (openInclusionImage_le (U k) ⊤) 1)

theorem openFrameLocalSection_app (k : ι) (W : (U k).toScheme.Opens) (r : Γ((U k).toScheme, W)) :
    (openFrameLocalSection D k).app W r =
      SectionGenerators.openFrameGenerator D ((U k).ι ''ᵁ W) k (openInclusionImage_le (U k) W)
        (((U k).ι.appIso W).inv r) := by
  let f := (U k).ι
  let V₀ := f ''ᵁ (⊤ : (U k).toScheme.Opens)
  let V := f ''ᵁ W
  have h : V ≤ V₀ := f.image_mono le_top
  have hg : RestrictionCompatibility.openFrameSectionRestriction D h
      (SectionGenerators.openFrameGenerator D V₀ k (openInclusionImage_le (U k) ⊤) 1) =
        SectionGenerators.openFrameGenerator D V k (openInclusionImage_le (U k) W) 1 :=
    (GeneratorNaturality.openFrameGenerator_restriction D h k (openInclusionImage_le (U k) ⊤) 1).trans
      (congrArg (SectionGenerators.openFrameGenerator D V k (openInclusionImage_le (U k) W))
        (X.presheaf.map (homOfLE h).op).hom.map_one)
  refine (Global.SectionMapValues.moduleSectionHomEquiv_symm_app ((ModuleSheaf.openFrameModuleSheaf D).restrict f)
    (SectionGenerators.openFrameGenerator D V₀ k (openInclusionImage_le (U k) ⊤) 1) W r).trans ?_
  change ((f.appIso W).inv r) • RestrictionCompatibility.openFrameSectionRestriction D h
      (SectionGenerators.openFrameGenerator D V₀ k (openInclusionImage_le (U k) ⊤) 1) =
    SectionGenerators.openFrameGenerator D V k (openInclusionImage_le (U k) W) ((f.appIso W).inv r)
  exact (congrArg (fun z : SectionModules.openFrameSectionModule U D V => ((f.appIso W).inv r) • z) hg).trans
    (GeneratorNaturality.openFrameGenerator_smul_one D V k (openInclusionImage_le (U k) W) ((f.appIso W).inv r))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalSections
