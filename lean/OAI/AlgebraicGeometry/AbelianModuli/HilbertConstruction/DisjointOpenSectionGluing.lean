import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmptyModuleSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsOnOpenImages

/-! # Disjoint Open Section Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DisjointOpenSectionGluing

noncomputable section

/-! Arbitrary actual sections on a disjoint open cover glue uniquely without compatibility conditions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem moduleSection_glue_on_disjoint_open_images
    {X : Scheme.{u}} (M : X.Modules) {ι : Type v}
    (T : ι → Scheme.{u}) (g : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (g i)]
    (hg : ∀ x : X, ∃ i, x ∈ g i ''ᵁ (⊤ : (T i).Opens))
    (hdis : Pairwise (fun i j => Disjoint (g i ''ᵁ (⊤ : (T i).Opens)) (g j ''ᵁ (⊤ : (T j).Opens))))
    (s : ∀ i, Line.Bundles.structureModule (T i) ⟶ (Scheme.Modules.pullback (g i)).obj M) :
    ∃! t : Line.Bundles.structureModule X ⟶ M, ∀ i, Ample.LineBundles.pullbackSection (g i) t = s i := by
  apply SectionsOnOpenImages.moduleSection_glue_on_open_images M T g hg s
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · have h := EmptyModuleSections.moduleSections_subsingleton_of_empty M (disjoint_iff.mp (hdis hij))
    exact h.elim _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DisjointOpenSectionGluing
