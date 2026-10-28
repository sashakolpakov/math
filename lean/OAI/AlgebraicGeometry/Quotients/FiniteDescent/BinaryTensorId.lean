import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange

/-! # Binary Tensor Id -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap

noncomputable section

/-! Functorial maps of the actual binary tensor sheaf and tensor products of sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory

universe u

variable {X : Scheme.{u}}

local instance : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

def map {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ⟶ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M' N' :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (f.val ⊗ₘ g.val)

theorem map_id (M N : X.Modules) : BinaryTensorMap.map (𝟙 M) (𝟙 N) = 𝟙 (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) := by
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (𝟙 M.val ⊗ₘ 𝟙 N.val) = _
  rw [id_tensorHom_id]
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_id _

theorem map_comp {M₁ M₂ M₃ N₁ N₂ N₃ : X.Modules}
    (f : M₁ ⟶ M₂) (f' : M₂ ⟶ M₃) (g : N₁ ⟶ N₂) (g' : N₂ ⟶ N₃) :
    BinaryTensorMap.map (f ≫ f') (g ≫ g') = BinaryTensorMap.map f g ≫ BinaryTensorMap.map f' g' := by
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((f.val ≫ f'.val) ⊗ₘ (g.val ≫ g'.val)) = _
  rw [← tensorHom_comp_tensorHom, Functor.map_comp]
  rfl

instance map_isIso {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N')
    [IsIso f] [IsIso g] : IsIso (BinaryTensorMap.map f g) := by
  refine ⟨⟨BinaryTensorMap.map (inv f) (inv g), ?_, ?_⟩⟩
  · rw [← BinaryTensorMap.map_comp, IsIso.hom_inv_id, IsIso.hom_inv_id, BinaryTensorMap.map_id]
  · rw [← BinaryTensorMap.map_comp, IsIso.inv_hom_id, IsIso.inv_hom_id, BinaryTensorMap.map_id]

theorem map_iso {M M' N N' : X.Modules} (e : M ≅ M') (e' : N ≅ N') :
    BinaryTensorMap.map e.hom e'.hom = (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr e e').hom := rfl

def tensorSection {M N : X.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N :=
  (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).inv ≫ BinaryTensorMap.map s t

instance section_isIso {M N : X.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N) [IsIso s] [IsIso t] : IsIso (tensorSection s t) := by
  dsimp [tensorSection]
  infer_instance

theorem section_postcomp {M M' N N' : X.Modules}
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N) (f : M ⟶ M') (g : N ⟶ N') :
    tensorSection (s ≫ f) (t ≫ g) = tensorSection s t ≫ BinaryTensorMap.map f g := by
  simp only [tensorSection, BinaryTensorMap.map_comp, Category.assoc]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap
