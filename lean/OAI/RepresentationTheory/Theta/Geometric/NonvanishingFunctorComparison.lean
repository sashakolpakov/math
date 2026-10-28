import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing
import OAI.RepresentationTheory.Theta.Geometric.Pullback.Algebraic

/-! # Nonvanishing Functor Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric.NonvanishingFunctorComparison

noncomputable section

/-! Nonvanishing is invariant under the canonical comparison of module
functors and their structure-module frames. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem sectionNonvanishing_functorComparison {X Y : Scheme.{u}}
    (F G : Y.Modules ⥤ X.Modules) (e : F ≅ G)
    (uF : F.obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (uG : G.obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    {M : Y.Modules} (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (uG.inv ≫ G.map s) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (uF.inv ≫ F.map s) := by
  have h := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Comparison.framedSection_functorComparison F G e uF uG s
  rw [← h, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction.sectionNonvanishing_sourceIso]

theorem sectionNonvanishing_pullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z ⟶ M) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g s)) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (f ≫ g) s) := by
  have h := sectionNonvanishing_functorComparison
    (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f) (Scheme.Modules.pullback (f ≫ g))
    (Scheme.Modules.pullbackComp f g)
    ((Scheme.Modules.pullback f).mapIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g) ≪≫ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f)
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f ≫ g)) s
  simpa only [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Iso.trans_inv, Functor.mapIso_inv, Functor.comp_map,
    Functor.map_comp, Category.assoc] using h.symm

theorem sectionNonvanishing_pullback_targetIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M) (e : M ≅ N) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (s ≫ e.hom)) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) := by
  have h : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (s ≫ e.hom) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s ≫ ((Scheme.Modules.pullback f).mapIso e).hom := by
    simp only [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Functor.map_comp, Functor.mapIso_hom, Category.assoc]
  rw [h, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso]

end

end OAI.RepresentationTheory.Theta.Geometric.NonvanishingFunctorComparison
