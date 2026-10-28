import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Bifunctor

/-! # Map Sheafification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.MapSheafification

noncomputable section

/-! The functorial map on the actual sheaf tensor product is the sheafification of the pointwise tensor map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
universe u

local instance traceMapPresheafMonoidal (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

theorem tensorModuleMap_eq_sheafification {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') :
    Bifunctor.tensorModuleMap f g =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (f.val ⊗ₘ g.val) := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  rw [Bifunctor.tensorModuleMap, Equiv.apply_symm_apply]
  have hh : ProductSheaf.tensorModuleHomEquiv M N (ProductSheaf.tensorModule M' N')
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (f.val ⊗ₘ g.val)) =
      (f.val ⊗ₘ g.val) ≫ ProductSheaf.tensorModuleHomEquiv M' N' _ (𝟙 (ProductSheaf.tensorModule M' N')) := by
    have ht :=
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_left
        (f.val ⊗ₘ g.val) (𝟙 (ProductSheaf.tensorModule M' N'))
    let k : ProductSheaf.tensorModule M N ⟶ ProductSheaf.tensorModule M' N' :=
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (f.val ⊗ₘ g.val)
    exact (congrArg (ProductSheaf.tensorModuleHomEquiv M N (ProductSheaf.tensorModule M' N'))
      (Category.comp_id k)).symm.trans ht
  have he : (Bifunctor.tensorBilinear M' N').precomp f g = Bilinear.Sheaves.SheafBilinearMap.ofTensorPresheafHom
      ((f.val ⊗ₘ g.val) ≫ ProductSheaf.tensorModuleHomEquiv M' N' _ (𝟙 (ProductSheaf.tensorModule M' N'))) := by
    ext U x y
    rfl
  exact he.trans (congrArg (Bilinear.Sheaves.SheafBilinearMap.ofTensorPresheafHom
    (M := M) (N := N) (P := ProductSheaf.tensorModule M' N')) hh).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.MapSheafification
