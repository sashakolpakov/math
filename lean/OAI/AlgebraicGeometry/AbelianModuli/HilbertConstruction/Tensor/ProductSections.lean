import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackUnits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Product Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSections

noncomputable section

/-! Products of sections of module sheaves and their scalar formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def tensorProductSection {L M : X.Modules}
    (s : Line.Bundles.structureModule X ⟶ L) (t : Line.Bundles.structureModule X ⟶ M) :
    Line.Bundles.structureModule X ⟶ ProductSheaf.tensorModule L M :=
  (ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)).inv ≫ Bifunctor.tensorModuleMap s t

theorem tensorProductSection_postcomp {L L' M M' : X.Modules}
    (s : Line.Bundles.structureModule X ⟶ L) (t : Line.Bundles.structureModule X ⟶ M) (a : L ⟶ L') (b : M ⟶ M') :
    tensorProductSection s t ≫ Bifunctor.tensorModuleMap a b = tensorProductSection (s ≫ a) (t ≫ b) := by
  rw [tensorProductSection, Category.assoc, Bifunctor.tensorModuleMap_comp]
  rfl

instance tensorProductSection_isIso {L M : X.Modules}
    (s : Line.Bundles.structureModule X ⟶ L) (t : Line.Bundles.structureModule X ⟶ M) [IsIso s] [IsIso t] :
    IsIso (tensorProductSection s t) := by
  dsimp only [tensorProductSection]
  infer_instance

theorem tensorModuleMap_unit_formula (a b : End (Line.Bundles.structureModule X)) :
    Bifunctor.tensorModuleMap a b ≫ (ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)).hom =
      (ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)).hom ≫ a ≫ b := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (Line.Bundles.structureModule X) (Line.Bundles.structureModule X) _).injective
  rw [PullbackComparison.tensorHomEquiv_precomp, PullbackUnits.tensorModuleUnitLeftIso_formula,
    Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, PullbackUnits.tensorModuleUnitLeftIso_formula]
  apply Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply DFunLike.ext
  intro r
  apply DFunLike.ext
  intro s
  change Γ(X, U) at r s
  change (show Γ(X, U) from a.app U r) * (show Γ(X, U) from b.app U s) =
    (show Γ(X, U) from b.app U (a.app U (r * s)))
  rw [TensorPower.Units.structureModuleEnd_app a U r, TensorPower.Units.structureModuleEnd_app b U s,
    TensorPower.Units.structureModuleEnd_app a U (r * s),
    TensorPower.Units.structureModuleEnd_app b U ((r * s) * (show Γ(X, U) from a.app U (1 : Γ(X, U))))]
  ring

theorem tensorProductSection_unit_formula (a b : End (Line.Bundles.structureModule X)) :
    tensorProductSection a b ≫ (ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)).hom = a ≫ b := by
  rw [tensorProductSection, Category.assoc, tensorModuleMap_unit_formula,
    Iso.inv_hom_id_assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSections
