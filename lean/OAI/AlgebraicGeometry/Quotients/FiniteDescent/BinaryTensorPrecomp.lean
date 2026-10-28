import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorId

/-! # Binary Tensor Precomp -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorPrecomp.Construction.BinaryTensorUniversal

noncomputable section

/-! Universal bilinear formulas for binary tensor-sheaf maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory

universe u

variable {X : Scheme.{u}}

local instance : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

def bilinear (M N : X.Modules) : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) :=
  AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _ (𝟙 _)

theorem postcomp {M N P : X.Modules} (h : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ⟶ P) :
    (bilinear M N).postcomp h = AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P h := by
  have he := AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp (𝟙 (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)) h
  simpa only [bilinear, Category.id_comp] using he.symm

theorem hom_ext {M N P : X.Modules} {a b : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ⟶ P}
    (h : (bilinear M N).postcomp a = (bilinear M N).postcomp b) : a = b := by
  rw [BinaryTensorUniversal.postcomp, BinaryTensorUniversal.postcomp] at h
  exact (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P).injective h

theorem precomp {M M' N N' P : X.Modules} (f : M ⟶ M') (g : N ⟶ N')
    (h : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M' N' ⟶ P) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P (BinaryTensorId.Construction.BinaryTensorMap.map f g ≫ h) =
      (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M' N' P h).precomp f g := by
  have he := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_left (f.val ⊗ₘ g.val) h
  change AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ofTensorPresheafHom
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleHomEquiv M N P (BinaryTensorId.Construction.BinaryTensorMap.map f g ≫ h)) = _
  rw [show AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleHomEquiv M N P (BinaryTensorId.Construction.BinaryTensorMap.map f g ≫ h) =
    (f.val ⊗ₘ g.val) ≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleHomEquiv M' N' P h from he]
  ext U x y
  rfl

theorem map_spec {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    (bilinear M N).postcomp (BinaryTensorId.Construction.BinaryTensorMap.map f g) = (bilinear M' N').precomp f g := by
  rw [BinaryTensorUniversal.postcomp]
  simpa only [bilinear, Category.comp_id] using BinaryTensorUniversal.precomp f g (𝟙 (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M' N'))

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorPrecomp.Construction.BinaryTensorUniversal
