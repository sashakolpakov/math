import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.SchemeFiniteType

/-! # Scheme Universal Trivialization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! The frame scheme carries an actual universal line-bundle
trivialization, constructed even when the frame scheme is not affine. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u
variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} [IsProper π] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)

abbrev Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameFamily : Scheme.{u} := pullback (pullback.snd π D.scheme.hom) D.frameOpen.ι

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameFamilyToOriginal : D.frameFamily ⟶ X :=
  pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι ≫ pullback.fst π D.scheme.hom

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameFamilyProjection : D.frameFamily ⟶ D.frameSchemeOverBase.left :=
  pullback.snd (pullback.snd π D.scheme.hom) D.frameOpen.ι

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameFamily_isPullback :
    IsPullback D.frameFamilyToOriginal D.frameFamilyProjection π D.frameSchemeOverBase.hom :=
  (IsPullback.of_hasPullback (pullback.snd π D.scheme.hom) D.frameOpen.ι).paste_horiz
    (IsPullback.of_hasPullback π D.scheme.hom)

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.tautologicalFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule D.frameFamily ≅
    (Scheme.Modules.pullback D.frameFamilyToOriginal).obj L.sheaf := by
  let j := pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι
  haveI : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j D.universalSectionHom) :=
    (D.universalSectionHom_isIso_iff j (pullback.snd (pullback.snd π D.scheme.hom) D.frameOpen.ι)
      D.frameOpen.ι (IsPullback.of_hasPullback (pullback.snd π D.scheme.hom) D.frameOpen.ι)).mpr
      (fun y => y.property)
  exact asIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j D.universalSectionHom) ≪≫
    (Scheme.Modules.pullbackComp j (pullback.fst π D.scheme.hom)).app L.sheaf

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.tautologicalFrame_value :
    AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback D.frameFamilyToOriginal).obj L.sheaf) D.tautologicalFrame.hom =
    GlobalSectionComposition.Construction.globalSectionCompositePullback (pullback.fst π D.scheme.hom)
      (pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι) L.sheaf D.universalSection := by
  have he := GlobalSectionHomPullback.Construction.moduleSectionHomEquiv_composite (pullback.fst π D.scheme.hom)
    (pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι) L.sheaf D.universalSectionHom
  change AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback D.frameFamilyToOriginal).obj L.sheaf) D.tautologicalFrame.hom =
    GlobalSectionComposition.Construction.globalSectionCompositePullback (pullback.fst π D.scheme.hom)
      (pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι) L.sheaf
        (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv D.universalLineBundle.sheaf D.universalSectionHom) at he
  rw [D.universalSectionHom_value] at he
  exact he

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
