import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.SchemeClassification

/-! # Scheme Naturality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! The frame-scheme classification respects the actual pullback of
line-bundle trivializations and the pullback composition isomorphism. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

def Frame.SchemeNaturality.Construction.compositeLineFrameIso {X Y Z : Scheme.{u}} (f : Y ⟶ X) (j : Z ⟶ Y) (M : X.Modules)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z ≅ (Scheme.Modules.pullback (j ≫ f)).obj M :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso j).symm ≪≫ (Scheme.Modules.pullback j).mapIso e ≪≫
    (Scheme.Modules.pullbackComp j f).app M

theorem Frame.SchemeNaturality.Construction.compositeLineFrameIso_value {X Y Z : Scheme.{u}} (f : Y ⟶ X) (j : Z ⟶ Y) (M : X.Modules)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj M) :
    AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback (j ≫ f)).obj M) (Frame.SchemeNaturality.Construction.compositeLineFrameIso f j M e).hom =
      GlobalSectionComposition.Construction.globalSectionCompositePullback f j M (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback f).obj M) e.hom) :=
  GlobalSectionHomPullback.Construction.moduleSectionHomEquiv_composite f j M e.hom

variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} [IsProper π] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.lineBundleTrivializationPointEquiv_inclusion {Y T : Scheme.{u}} [IsAffine T]
    (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback f ρ π g)
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf) :
    D.lineBundleTrivializationPointEquiv f ρ g hp e ≫ OpenFamilyPoints.Construction.openFamilyInclusion D.scheme D.frameOpen =
      D.sectionPointEquiv f ρ g hp (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback f).obj L.sheaf) e.hom) :=
  D.framePointEquiv_inclusion f ρ g hp (Frame.SchemeClassification.Construction.moduleIsoFrameValues ((Scheme.Modules.pullback f).obj L.sheaf) e)

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.lineBundleTrivializationPointEquiv_natural {Y Z T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (f : Y ⟶ X) (j : Z ⟶ Y) (ρ : Y ⟶ T) (τ : Z ⟶ T') (g : T ⟶ S) (t : T' ⟶ T)
    (hp : IsPullback f ρ π g) (hj : j ≫ ρ = τ ≫ t) (ho : IsPullback (j ≫ f) τ π (t ≫ g))
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf) :
    D.lineBundleTrivializationPointEquiv (j ≫ f) τ (t ≫ g) ho (Frame.SchemeNaturality.Construction.compositeLineFrameIso f j L.sheaf e) =
      (Over.homMk t rfl : Over.mk (t ≫ g) ⟶ Over.mk g) ≫ D.lineBundleTrivializationPointEquiv f ρ g hp e := by
  have : Mono (OpenFamilyPoints.Construction.openFamilyInclusion D.scheme D.frameOpen) :=
    inferInstanceAs (Mono (Over.homMk D.frameOpen.ι rfl : OpenFamilyPoints.Construction.openFamily D.scheme D.frameOpen ⟶ D.scheme))
  apply (cancel_mono (OpenFamilyPoints.Construction.openFamilyInclusion D.scheme D.frameOpen)).mp
  rw [D.lineBundleTrivializationPointEquiv_inclusion, Category.assoc,
    D.lineBundleTrivializationPointEquiv_inclusion, Frame.SchemeNaturality.Construction.compositeLineFrameIso_value]
  exact D.sectionPointEquiv_natural f j ρ τ g t hp hj ho _

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
