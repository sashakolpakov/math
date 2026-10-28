import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSections

/-! # Tensor Section Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.TensorSectionFormula

noncomputable section

/-! The tensor product of a scalar section and a module section is ordinary precomposition, under the canonical tensor-unit isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem tensorModuleUnitLeftIso_naturality {X : Scheme.{u}} {M N : X.Modules} (s : M ⟶ N) :
    Tensor.Bifunctor.tensorModuleMap (𝟙 (Line.Bundles.structureModule X)) s ≫ (Tensor.ProductSheaf.tensorModuleUnitLeftIso N).hom =
      (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom ≫ s := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (Line.Bundles.structureModule X) M N).injective
  rw [Tensor.PullbackComparison.tensorHomEquiv_precomp, Tensor.PullbackUnits.tensorModuleUnitLeftIso_formula,
    Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, Tensor.PullbackUnits.tensorModuleUnitLeftIso_formula]
  apply Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply DFunLike.ext
  intro r
  apply DFunLike.ext
  intro m
  exact (s.app_smul r m).symm

theorem tensorProductSection_unitLeft_formula {X : Scheme.{u}} {M : X.Modules}
    (a : End (Line.Bundles.structureModule X)) (s : Line.Bundles.structureModule X ⟶ M) :
    Tensor.ProductSections.tensorProductSection a s ≫ (Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom = a ≫ s := by
  have h := Tensor.ProductSections.tensorProductSection_postcomp a (𝟙 (Line.Bundles.structureModule X)) (𝟙 (Line.Bundles.structureModule X)) s
  simp only [Category.comp_id, Category.id_comp] at h
  rw [← h, Category.assoc, tensorModuleUnitLeftIso_naturality, ← Category.assoc,
    Tensor.ProductSections.tensorProductSection_unit_formula, Category.comp_id]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.TensorSectionFormula
