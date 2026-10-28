import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionMultiplication
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Pullback Section Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.PullbackSectionBound

noncomputable section

/-! A generating family supplies a generically nonvanishing pulled-back section; a tensor identity then bounds the other factor's actual section space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X Y : Scheme.{u}}

theorem generatingSections_pullback_nonempty [Nonempty X] (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y)
    {ι : Type v} (s : ι → (Line.Bundles.structureModule Y ⟶ L.sheaf))
    (hs : ∀ y : Y, ∃ i, y ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    ∃ i, Nonempty (Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f (s i))) := by
  let x : X := Classical.choice inferInstance
  obtain ⟨i, hi⟩ := hs (f x)
  refine ⟨i, ⟨⟨x, ?_⟩⟩⟩
  rw [LineBundle.NonvanishingBaseChange.sectionNonvanishing_lineBundle_baseChange f L]
  exact hi

variable {K : Type u} [Field K] [IsIntegral X]

theorem tensorFactorSections_finite (p : X ⟶ Spec (.of K)) (L M B : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) [Nonempty (Ample.LineBundles.sectionNonvanishing s)]
    (e : (L.tensor M).sheaf ≅ B.sheaf)
    [Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj B.sheaf)] :
    Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M.sheaf) := by
  let a := ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).map
    (LineBundle.SectionMultiplication.lineBundleSectionMultiply L M s ≫ e.hom)).hom
  have ha : Function.Injective a :=
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso p e).injective.comp (LineBundle.SectionMultiplication.lineBundleSectionMultiply_sections_injective p L M s)
  exact Module.Finite.of_injective a ha

theorem tensorFactorSections_finrank_le (p : X ⟶ Spec (.of K)) (L M B : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) [Nonempty (Ample.LineBundles.sectionNonvanishing s)]
    (e : (L.tensor M).sheaf ≅ B.sheaf)
    [Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj B.sheaf)] :
    Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M.sheaf) ≤
      Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj B.sheaf) := by
  let a := ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).map
    (LineBundle.SectionMultiplication.lineBundleSectionMultiply L M s ≫ e.hom)).hom
  have ha : Function.Injective a :=
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso p e).injective.comp (LineBundle.SectionMultiplication.lineBundleSectionMultiply_sections_injective p L M s)
  exact LinearMap.finrank_le_finrank_of_injective ha

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.PullbackSectionBound
