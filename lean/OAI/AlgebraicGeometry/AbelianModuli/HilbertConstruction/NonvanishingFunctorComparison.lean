import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.PullbackCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction

/-! # Nonvanishing Functor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingFunctorComparison

noncomputable section

/-! Nonvanishing is independent of the canonical choices in composite pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem sectionNonvanishing_functorComparison (F G : Y.Modules ⥤ X.Modules) (e : F ≅ G)
    (uF : F.obj (Line.Bundles.structureModule Y) ≅ Line.Bundles.structureModule X)
    (uG : G.obj (Line.Bundles.structureModule Y) ≅ Line.Bundles.structureModule X)
    {L : Y.Modules} (s : Line.Bundles.structureModule Y ⟶ L) :
    Ample.LineBundles.sectionNonvanishing (uG.inv ≫ G.map s) = Ample.LineBundles.sectionNonvanishing (uF.inv ≫ F.map s) := by
  rw [← Frame.Comparison.framedSection_functorComparison F G e uF uG s]
  exact (Ample.Powers.sectionNonvanishing_comp_iso _ (e.app L)).trans (Section.SectionRestriction.sectionNonvanishing_sourceIso _ _)

theorem sectionNonvanishing_pullback_comp (f : Y ⟶ Z) (h : X ⟶ Y) {L : Z.Modules}
    (s : Line.Bundles.structureModule Z ⟶ L) :
    Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection h (Ample.LineBundles.pullbackSection f s)) =
      Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection (h ≫ f) s) := by
  have he := sectionNonvanishing_functorComparison
    (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback h) (Scheme.Modules.pullback (h ≫ f))
    (Scheme.Modules.pullbackComp h f) (Frame.PullbackCoherence.structureModuleIteratedPullbackIso f h)
    (Line.Bundles.structureModulePullbackIso (h ≫ f)) s
  exact (congrArg Ample.LineBundles.sectionNonvanishing (Frame.PullbackCoherence.section_iteratedPullback f h s)).symm.trans he.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingFunctorComparison
