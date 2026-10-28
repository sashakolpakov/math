import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenExtensionComposition

/-! # Chart Extension Factorization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ChartExtensionFactorization.Constructions

noncomputable section

/-! Factorization of actual compact-support extension through chart coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem openExtension_chartFactorization {X Y Z W : TopCat.{0}}
    [T2Space Y] [T2Space Z] [T2Space W]
    (e : X ≃ₜ Y) (f : Y ⟶ Z) (g : Z ≃ₜ W) (hf : Topology.IsOpenEmbedding f) (n : ℕ) :
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension
      ((TopCat.isoOfHomeo (X := X) (Y := Y) e).hom ≫ f ≫
        (TopCat.isoOfHomeo (X := Z) (Y := W) g).hom)
      ((g.isOpenEmbedding.comp hf).comp e.isOpenEmbedding) n =
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ) e n).inv ≫
      OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension f hf n ≫
      (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ) g n).inv := by
  rw [← OpenExtensionComposition.Constructions.openEmbeddingCompactExtension_comp (TopCat.isoOfHomeo (X := X) (Y := Y) e).hom
    (f ≫ (TopCat.isoOfHomeo (X := Z) (Y := W) g).hom)
    e.isOpenEmbedding (g.isOpenEmbedding.comp hf),
    ← OpenExtensionComposition.Constructions.openEmbeddingCompactExtension_comp f (TopCat.isoOfHomeo (X := Z) (Y := W) g).hom
      hf g.isOpenEmbedding,
    OpenExtensionComposition.Constructions.openEmbeddingCompactExtension_homeomorph e,
    OpenExtensionComposition.Constructions.openEmbeddingCompactExtension_homeomorph g]

theorem moduleIso_trace_of_inverse {A B C : ModuleCat.{0} ℚ} (e : A ≅ B)
    (a : A ⟶ C) (b : B ⟶ C) (h : e.inv ≫ a = b) : e.hom ≫ b = a := by
  rw [← h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ChartExtensionFactorization.Constructions
