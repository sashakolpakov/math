import OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorPullback
import OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHomMaps

/-! # Tensor Functors -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorFunctors

noncomputable section

/-! Tensor and internal Hom as adjoint functors on actual module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} {L L' M M' N P Q : X.Modules}

local instance : MonoidalCategory X.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory

def tensorModuleMap (f : L ⟶ L') (g : M ⟶ M') : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M ⟶ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L' M' :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (f.val ⊗ₘ g.val)

theorem tensorModuleMap_id (L M : X.Modules) : tensorModuleMap (𝟙 L) (𝟙 M) = 𝟙 _ := by
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((𝟙 L.val) ⊗ₘ (𝟙 M.val)) = _
  erw [id_tensorHom_id, CategoryTheory.Functor.map_id]
  rfl

theorem tensorModuleMap_comp (f : L ⟶ L') (f' : L' ⟶ N) (g : M ⟶ M') (g' : M' ⟶ P) :
    tensorModuleMap f g ≫ tensorModuleMap f' g' = tensorModuleMap (f ≫ f') (g ≫ g') := by
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (f.val ⊗ₘ g.val) ≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (f'.val ⊗ₘ g'.val) = _
  rw [← Functor.map_comp, tensorHom_comp_tensorHom]
  rfl

def tensorModuleRightFunctor (N : X.Modules) : X.Modules ⥤ X.Modules where
  obj M := AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N
  map f := tensorModuleMap f (𝟙 N)
  map_id M := tensorModuleMap_id M N
  map_comp f g := by rw [tensorModuleMap_comp, Category.id_comp]

def moduleInternalHomFunctor (N : X.Modules) : X.Modules ⥤ X.Modules where
  obj P := InternalHom.Construction.moduleInternalHom N P
  map f := InternalHomMaps.Construction.moduleInternalHomMap (𝟙 N) f
  map_id P := InternalHomMaps.Construction.moduleInternalHomMap_id N P
  map_comp f g := by rw [InternalHomMaps.Construction.moduleInternalHomMap_comp, Category.id_comp]

theorem tensorModuleMap_homEquiv (f : L ⟶ L') (g : M ⟶ M') (h : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L' M' ⟶ P) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv L M P (tensorModuleMap f g ≫ h) =
      (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv L' M' P h).precomp f g := by
  let a := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  change AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ofTensorPresheafHom
      (a.homEquiv _ P ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (f.val ⊗ₘ g.val) ≫ h)) = _
  rw [a.homEquiv_naturality_left]
  ext U l m
  rfl

theorem sheafBilinearCurry_postcomp (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L M P) (h : P ⟶ Q) :
    TensorHom.Construction.sheafBilinearCurry (b.postcomp h) = TensorHom.Construction.sheafBilinearCurry b ≫ InternalHomMaps.Construction.moduleInternalHomMap (𝟙 M) h := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro l
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro m
  rfl

theorem sheafBilinearCurry_precomp_left (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L M P) (f : L' ⟶ L) :
    TensorHom.Construction.sheafBilinearCurry (b.precomp f (𝟙 M)) = f ≫ TensorHom.Construction.sheafBilinearCurry b := by
  apply TensorHom.Construction.sheafBilinearCurryEquiv.symm.injective
  change TensorHom.Construction.sheafBilinearUncurry (TensorHom.Construction.sheafBilinearCurry _) = TensorHom.Construction.sheafBilinearUncurry _
  rw [TensorHom.Construction.sheafBilinearUncurry_curry]
  ext U l m
  change b.app U (f.app U l) m = b.app U (L.presheaf.map (𝟙 U).op (f.app U l)) m
  rw [op_id, L.presheaf.map_id, AddCommGrpCat.id_apply]

theorem tensorInternalHomEquiv_naturality_left (f : L' ⟶ L) (h : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M ⟶ P) :
    TensorHom.Construction.tensorInternalHomEquiv L' M P (tensorModuleMap f (𝟙 M) ≫ h) =
      f ≫ TensorHom.Construction.tensorInternalHomEquiv L M P h := by
  change TensorHom.Construction.sheafBilinearCurry (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv L' M P _) = _
  rw [tensorModuleMap_homEquiv, sheafBilinearCurry_precomp_left]
  rfl

theorem tensorInternalHomEquiv_naturality_right (f : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M ⟶ P) (h : P ⟶ Q) :
    TensorHom.Construction.tensorInternalHomEquiv L M Q (f ≫ h) =
      TensorHom.Construction.tensorInternalHomEquiv L M P f ≫ InternalHomMaps.Construction.moduleInternalHomMap (𝟙 M) h := by
  change TensorHom.Construction.sheafBilinearCurry (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv L M Q _) = _
  rw [AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp, sheafBilinearCurry_postcomp]
  rfl

def tensorInternalHomAdjunction (N : X.Modules) :
    tensorModuleRightFunctor N ⊣ moduleInternalHomFunctor N :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M P => TensorHom.Construction.tensorInternalHomEquiv M N P
      homEquiv_naturality_left_symm := by
        intro M M' P f h
        apply (TensorHom.Construction.tensorInternalHomEquiv M N P).injective
        erw [Equiv.apply_symm_apply, tensorInternalHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
        rfl
      homEquiv_naturality_right := tensorInternalHomEquiv_naturality_right }

instance tensorModuleRightFunctor_preservesColimits (N : X.Modules) :
    CategoryTheory.Limits.PreservesColimits (tensorModuleRightFunctor N) :=
  (tensorInternalHomAdjunction N).leftAdjoint_preservesColimits

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorFunctors
