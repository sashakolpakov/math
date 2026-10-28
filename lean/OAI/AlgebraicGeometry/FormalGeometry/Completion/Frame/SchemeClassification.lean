import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClassifiedFrameCriterion
import OAI.AlgebraicGeometry.FormalGeometry.Completion.OpenFamilyPoints
import OAI.AlgebraicGeometry.FormalGeometry.Completion.IsomorphismHomSubtype

/-! # Scheme Classification -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! Actual trivializations of the pulled-back line bundle are classified
by morphisms into the universal frame scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

def Frame.SchemeClassification.Construction.moduleIsoFrameValues {X : Scheme.{u}} (M : X.Modules) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) ≃ { s : Γ(M, ⊤) // IsIso ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm s) } :=
  (IsomorphismHomSubtype.Construction.isoHomSubtypeEquiv (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M).trans
    ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).subtypeEquiv (fun f => by rw [Equiv.symm_apply_apply]))

variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} [IsProper π] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)
  {Y T : Scheme.{u}} [IsAffine T] (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S)
  (hp : IsPullback f ρ π g)

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.framePointEquiv :
    { s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj L.sheaf)).obj (op ⊤) //
      IsIso ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback f).obj L.sheaf)).symm s) } ≃
    (Over.mk g ⟶ D.frameSchemeOverBase) :=
  ((D.sectionPointEquiv f ρ g hp).subtypeEquiv
    (fun s => D.section_isFrame_iff_classifier_mem f ρ g hp s)).trans
      (OpenFamilyPoints.Construction.openFamilyPointEquiv D.scheme D.frameOpen (Over.mk g)).symm

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.lineBundleTrivializationPointEquiv :
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf) ≃
      (Over.mk g ⟶ D.frameSchemeOverBase) :=
  (Frame.SchemeClassification.Construction.moduleIsoFrameValues ((Scheme.Modules.pullback f).obj L.sheaf)).trans (D.framePointEquiv f ρ g hp)

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.framePointEquiv_inclusion
    (s : { s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj L.sheaf)).obj (op ⊤) //
      IsIso ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback f).obj L.sheaf)).symm s) }) :
    D.framePointEquiv f ρ g hp s ≫ OpenFamilyPoints.Construction.openFamilyInclusion D.scheme D.frameOpen =
      D.sectionPointEquiv f ρ g hp s.val :=
  OpenFamilyPoints.Construction.openFamilyLift_fac D.scheme D.frameOpen (Over.mk g) (D.sectionPointEquiv f ρ g hp s.val)
    ((D.section_isFrame_iff_classifier_mem f ρ g hp s.val).mp s.property)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
