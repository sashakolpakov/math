import OAI.AlgebraicGeometry.Picard.Homomorphisms.BilinearSheafification

/-! # Tensor Sheafification -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms

noncomputable section

/-! Sheafification commutes with the actual tensor product of module presheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} {M N : X.PresheafOfModules} {P Q : X.Modules}

def PresheafTensorHom.Construction.PresheafBilinearMap.postcomp (b : PresheafTensorHom.Construction.PresheafBilinearMap M N P) (f : P ⟶ Q) :
    PresheafTensorHom.Construction.PresheafBilinearMap M N Q where
  app U := (b.app U).compr₂ (AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp f U)
  naturality {_U _V} h m n :=
    (ConcreteCategory.congr_hom (f.mapPresheaf.naturality h.op) (b.app _ m n)).symm.trans
      (congrArg (fun s => f.app _ s) (b.naturality h m n))

def TensorSheafification.Construction.presheafBilinearOfTensorHom
    (f : PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M N ⟶ P.val) :
    PresheafTensorHom.Construction.PresheafBilinearMap M N P where
  app U := TensorProduct.curry (f.app (.op U)).hom
  naturality h m n := (PresheafOfModules.naturality_apply f h.op (m ⊗ₜ n)).symm

def TensorSheafification.Construction.presheafBilinearToTensorHom (b : PresheafTensorHom.Construction.PresheafBilinearMap M N P) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M N ⟶ P.val where
  app U := ModuleCat.ofHom (TensorProduct.lift (b.app U.unop))
  naturality {_U _V} h := ModuleCat.MonoidalCategory.tensor_ext
    (fun m n => (b.naturality h.unop m n).symm)

def TensorSheafification.Construction.presheafTensorHomEquiv (M N : X.PresheafOfModules) (P : X.Modules) :
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M N ⟶ P.val) ≃
      PresheafTensorHom.Construction.PresheafBilinearMap M N P where
  toFun := TensorSheafification.Construction.presheafBilinearOfTensorHom
  invFun := TensorSheafification.Construction.presheafBilinearToTensorHom
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    rfl
  right_inv b := by ext U m n; rfl

def TensorSheafification.Construction.sheafBilinearPresheafEquiv (M N P : X.Modules) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P ≃ PresheafTensorHom.Construction.PresheafBilinearMap M.val N.val P where
  toFun b := { app := b.app, naturality := b.naturality }
  invFun b := { app := b.app, naturality := b.naturality }
  left_inv b := by cases b; rfl
  right_inv b := by cases b; rfl

def TensorSheafification.Construction.sheafifiedTensorHomEquiv (M N : X.PresheafOfModules) (P : X.Modules) :
    (BilinearSheafification.Construction.moduleSheafify (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M N) ⟶ P) ≃
      PresheafTensorHom.Construction.PresheafBilinearMap M N P :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ P).trans
    (TensorSheafification.Construction.presheafTensorHomEquiv M N P)

theorem TensorSheafification.Construction.sheafifiedTensorHomEquiv_postcomp
    (f : BilinearSheafification.Construction.moduleSheafify (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M N) ⟶ P) (h : P ⟶ Q) :
    TensorSheafification.Construction.sheafifiedTensorHomEquiv M N Q (f ≫ h) = (TensorSheafification.Construction.sheafifiedTensorHomEquiv M N P f).postcomp h := by
  change TensorSheafification.Construction.presheafBilinearOfTensorHom
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ Q (f ≫ h)) = _
  rw [Adjunction.homEquiv_naturality_right]
  ext U m n
  rfl

def TensorSheafification.Construction.tensorSheafifyComparison (M N : X.PresheafOfModules) :
    BilinearSheafification.Construction.moduleSheafify (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M N) ⟶
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (BilinearSheafification.Construction.moduleSheafify M) (BilinearSheafification.Construction.moduleSheafify N) :=
  (TensorSheafification.Construction.sheafifiedTensorHomEquiv M N _).symm
    (BilinearSheafification.Construction.bilinearSheafifyEquiv M N _ (TensorSheafification.Construction.sheafBilinearPresheafEquiv _ _ _
      (TensorAssociativity.Construction.tensorModuleBilinear (BilinearSheafification.Construction.moduleSheafify M) (BilinearSheafification.Construction.moduleSheafify N))))

theorem TensorSheafification.Construction.tensorSheafifyComparison_homEquiv (M N : X.PresheafOfModules)
    (f : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (BilinearSheafification.Construction.moduleSheafify M) (BilinearSheafification.Construction.moduleSheafify N) ⟶ P) :
    TensorSheafification.Construction.sheafifiedTensorHomEquiv M N P (TensorSheafification.Construction.tensorSheafifyComparison M N ≫ f) =
      BilinearSheafification.Construction.bilinearSheafifyEquiv M N P (TensorSheafification.Construction.sheafBilinearPresheafEquiv _ _ _
        (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ f)) := by
  rw [TensorSheafification.Construction.sheafifiedTensorHomEquiv_postcomp, TensorSheafification.Construction.tensorSheafifyComparison, Equiv.apply_symm_apply,
    BilinearSheafification.Construction.bilinearSheafifyEquiv_apply, BilinearSheafification.Construction.bilinearSheafifyEquiv_apply, TensorAssociativity.Construction.tensorModuleBilinear_postcomp]
  ext U m n
  rfl

instance TensorSheafification.Construction.tensorSheafifyComparison_isIso (M N : X.PresheafOfModules) :
    IsIso (TensorSheafification.Construction.tensorSheafifyComparison M N) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro P
  let e := (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (BilinearSheafification.Construction.moduleSheafify M) (BilinearSheafification.Construction.moduleSheafify N) P).trans
    ((TensorSheafification.Construction.sheafBilinearPresheafEquiv _ _ P).trans
      ((BilinearSheafification.Construction.bilinearSheafifyEquiv M N P).trans (TensorSheafification.Construction.sheafifiedTensorHomEquiv M N P).symm))
  have he : (fun f : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (BilinearSheafification.Construction.moduleSheafify M) (BilinearSheafification.Construction.moduleSheafify N) ⟶ P =>
      TensorSheafification.Construction.tensorSheafifyComparison M N ≫ f) = e := by
    funext f
    apply (TensorSheafification.Construction.sheafifiedTensorHomEquiv M N P).injective
    exact (TensorSheafification.Construction.tensorSheafifyComparison_homEquiv M N f).trans
      ((TensorSheafification.Construction.sheafifiedTensorHomEquiv M N P).apply_symm_apply _).symm
  change Function.Bijective (fun f => TensorSheafification.Construction.tensorSheafifyComparison M N ≫ f)
  rw [he]
  exact e.bijective

def TensorSheafification.Construction.tensorSheafifyIso (M N : X.PresheafOfModules) :
    BilinearSheafification.Construction.moduleSheafify (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M N) ≅
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (BilinearSheafification.Construction.moduleSheafify M) (BilinearSheafification.Construction.moduleSheafify N) :=
  asIso (TensorSheafification.Construction.tensorSheafifyComparison M N)

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms
