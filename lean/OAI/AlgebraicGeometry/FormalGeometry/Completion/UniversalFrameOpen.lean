import OAI.AlgebraicGeometry.FormalGeometry.Completion.UniversalModelSection
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionHomPullback
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SectionFrameBaseChange

/-! # Universal Frame Open -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! The frame condition for the universal section defines an actual
open subset of the finite-type section scheme. Its pullback criterion
is expressed using the same global-section classification. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u
variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} [IsProper π] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.universalLineBundle : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle D.universalFamily := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (pullback.fst π D.scheme.hom) L

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.universalSectionHom : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule D.universalFamily ⟶ D.universalLineBundle.sheaf :=
  (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv D.universalLineBundle.sheaf).symm D.universalSection

omit [IsProper π] in
theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.universalSectionHom_value :
    AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv D.universalLineBundle.sheaf D.universalSectionHom = D.universalSection :=
  (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv D.universalLineBundle.sheaf).apply_symm_apply _

def Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.frameOpen : D.scheme.left.Opens :=
  Quotients.FiniteDescent.SectionTriviality.Construction.SectionTrivialityOpen.baseOpen (pullback.snd π D.scheme.hom) D.universalLineBundle D.universalSectionHom

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.universalSectionHom_isIso_iff {Z T : Scheme.{u}}
    (j : Z ⟶ D.universalFamily) (τ : Z ⟶ T) (t : T ⟶ D.scheme.left)
    (hp : IsPullback j τ (pullback.snd π D.scheme.hom) t) :
    IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j D.universalSectionHom) ↔ ∀ y : T, t y ∈ D.frameOpen :=
  SectionFrameBaseChange.Construction.pullbackSection_isIso_iff_baseOpen j (pullback.snd π D.scheme.hom) τ t hp
    D.universalLineBundle D.universalSectionHom

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.universalCompositeSection_isIso_iff {Z T : Scheme.{u}}
    (j : Z ⟶ D.universalFamily) (τ : Z ⟶ T) (t : T ⟶ D.scheme.left)
    (hp : IsPullback j τ (pullback.snd π D.scheme.hom) t) :
    IsIso ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback (j ≫ pullback.fst π D.scheme.hom)).obj L.sheaf)).symm
      (GlobalSectionComposition.Construction.globalSectionCompositePullback (pullback.fst π D.scheme.hom) j L.sheaf D.universalSection)) ↔
      ∀ y : T, t y ∈ D.frameOpen := by
  let e := AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback (j ≫ pullback.fst π D.scheme.hom)).obj L.sheaf)
  have he := GlobalSectionHomPullback.Construction.moduleSectionHomEquiv_composite (pullback.fst π D.scheme.hom) j L.sheaf D.universalSectionHom
  change e (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j D.universalSectionHom ≫
    (Scheme.Modules.pullbackComp j (pullback.fst π D.scheme.hom)).hom.app L.sheaf) =
      GlobalSectionComposition.Construction.globalSectionCompositePullback (pullback.fst π D.scheme.hom) j L.sheaf
        (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv D.universalLineBundle.sheaf D.universalSectionHom) at he
  rw [D.universalSectionHom_value] at he
  have hx := (congrArg e.symm he).symm.trans (e.symm_apply_apply _)
  change IsIso (e.symm _) ↔ _
  rw [hx]
  exact (isIso_comp_right_iff _ _).trans (D.universalSectionHom_isIso_iff j τ t hp)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
