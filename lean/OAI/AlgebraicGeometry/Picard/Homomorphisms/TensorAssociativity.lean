import OAI.AlgebraicGeometry.Picard.Homomorphisms.Trilinear
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles

/-! # Tensor Associativity -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms

noncomputable section

/-! Associativity of the actual tensor product, from trilinear universal properties. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} {L M N P Q : X.Modules}

def Trilinear.Construction.SheafTrilinearMap.postcomp (b : Trilinear.Construction.SheafTrilinearMap L M N P) (f : P ⟶ Q) :
    Trilinear.Construction.SheafTrilinearMap L M N Q where
  app U := (b.app U).compr₂
    (LinearMap.llcomp Γ(X, U) Γ(N, U) Γ(P, U) Γ(Q, U) (AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp f U))
  naturality {_U _V} h l m n :=
    (ConcreteCategory.congr_hom (f.mapPresheaf.naturality h.op) (b.app _ l m n)).symm.trans
      (congrArg (fun s => f.app _ s) (b.naturality h l m n))

def Trilinear.Construction.SheafTrilinearMap.rotate (b : Trilinear.Construction.SheafTrilinearMap L M N P) :
    Trilinear.Construction.SheafTrilinearMap N L M P where
  app U := (LinearMap.lflip.toLinearMap.comp (b.app U)).flip
  naturality f n l m := b.naturality f l m n

def Trilinear.Construction.SheafTrilinearMap.rotateEquiv : Trilinear.Construction.SheafTrilinearMap L M N P ≃ Trilinear.Construction.SheafTrilinearMap N L M P where
  toFun := Trilinear.Construction.SheafTrilinearMap.rotate
  invFun b := b.rotate.rotate
  left_inv b := by ext U l m n; rfl
  right_inv b := by ext U n l m; rfl

def TensorAssociativity.Construction.trilinearOutputFunctor (L M N : X.Modules) : X.Modules ⥤ Type u where
  obj P := Trilinear.Construction.SheafTrilinearMap L M N P
  map f := TypeCat.ofHom (fun b => b.postcomp f)
  map_id P := by ext b U l m n; rfl
  map_comp f g := by ext b U l m n; rfl

def TensorAssociativity.Construction.tensorModuleBilinear (L M : X.Modules) : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M) :=
  AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv L M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M) (𝟙 _)

theorem TensorAssociativity.Construction.tensorModuleBilinear_postcomp (f : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M ⟶ P) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv L M P f = (TensorAssociativity.Construction.tensorModuleBilinear L M).postcomp f := by
  have he := AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp (𝟙 (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M)) f
  rw [Category.id_comp] at he
  exact he

def TensorAssociativity.Construction.tensorLeftTrilinearEquiv (L M N P : X.Modules) :
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M) N ⟶ P) ≃ Trilinear.Construction.SheafTrilinearMap L M N P :=
  (TensorHom.Construction.tensorInternalHomEquiv (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M) N P).trans
    ((AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv L M (InternalHom.Construction.moduleInternalHom N P)).trans Trilinear.Construction.bilinearHomTrilinearEquiv)

theorem TensorAssociativity.Construction.tensorLeftTrilinearEquiv_apply (f : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M) N ⟶ P)
    (U : X.Opens) (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
    (TensorAssociativity.Construction.tensorLeftTrilinearEquiv L M N P f).app U l m n =
      f.app U ((TensorAssociativity.Construction.tensorModuleBilinear (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M) N).app U
        ((TensorAssociativity.Construction.tensorModuleBilinear L M).app U l m) n) := by
  change TensorHom.Construction.internalHomEval N P U
    ((AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv L M (InternalHom.Construction.moduleInternalHom N P)
      (TensorHom.Construction.sheafBilinearCurry (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M) N P f))).app U l m) n = _
  rw [TensorAssociativity.Construction.tensorModuleBilinear_postcomp]
  change (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M) N P f).app U
    ((AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M).presheaf.map (𝟙 U).op ((TensorAssociativity.Construction.tensorModuleBilinear L M).app U l m)) n = _
  rw [op_id, (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M).presheaf.map_id, AddCommGrpCat.id_apply,
    TensorAssociativity.Construction.tensorModuleBilinear_postcomp]
  rfl

theorem TensorAssociativity.Construction.tensorLeftTrilinearEquiv_postcomp (f : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M) N ⟶ P)
    (h : P ⟶ Q) :
    TensorAssociativity.Construction.tensorLeftTrilinearEquiv L M N Q (f ≫ h) =
      (TensorAssociativity.Construction.tensorLeftTrilinearEquiv L M N P f).postcomp h := by
  ext U l m n
  change (TensorAssociativity.Construction.tensorLeftTrilinearEquiv L M N Q (f ≫ h)).app U l m n =
    h.app U ((TensorAssociativity.Construction.tensorLeftTrilinearEquiv L M N P f).app U l m n)
  rw [TensorAssociativity.Construction.tensorLeftTrilinearEquiv_apply, TensorAssociativity.Construction.tensorLeftTrilinearEquiv_apply]
  rfl

def TensorAssociativity.Construction.tensorRightTrilinearEquiv (L M N P : X.Modules) :
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ⟶ P) ≃ Trilinear.Construction.SheafTrilinearMap L M N P :=
  (Iso.homCongr (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso L (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)) (Iso.refl P)).trans
    ((TensorAssociativity.Construction.tensorLeftTrilinearEquiv M N L P).trans Trilinear.Construction.SheafTrilinearMap.rotateEquiv)

theorem TensorAssociativity.Construction.tensorRightTrilinearEquiv_postcomp (f : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ⟶ P)
    (h : P ⟶ Q) :
    TensorAssociativity.Construction.tensorRightTrilinearEquiv L M N Q (f ≫ h) =
      (TensorAssociativity.Construction.tensorRightTrilinearEquiv L M N P f).postcomp h := by
  change (TensorAssociativity.Construction.tensorLeftTrilinearEquiv M N L Q
      ((AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso L (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)).inv ≫ (f ≫ h) ≫ 𝟙 Q)).rotate =
    (TensorAssociativity.Construction.tensorLeftTrilinearEquiv M N L P
      ((AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso L (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)).inv ≫ f ≫ 𝟙 P)).rotate.postcomp h
  rw [Category.comp_id, Category.comp_id, ← Category.assoc, TensorAssociativity.Construction.tensorLeftTrilinearEquiv_postcomp]
  ext U l m n
  rfl

def TensorAssociativity.Construction.tensorLeftTrilinearCorepresentable (L M N : X.Modules) :
    (TensorAssociativity.Construction.trilinearOutputFunctor L M N).CorepresentableBy (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M) N) where
  homEquiv := TensorAssociativity.Construction.tensorLeftTrilinearEquiv L M N _
  homEquiv_comp h f := TensorAssociativity.Construction.tensorLeftTrilinearEquiv_postcomp f h

def TensorAssociativity.Construction.tensorRightTrilinearCorepresentable (L M N : X.Modules) :
    (TensorAssociativity.Construction.trilinearOutputFunctor L M N).CorepresentableBy (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)) where
  homEquiv := TensorAssociativity.Construction.tensorRightTrilinearEquiv L M N _
  homEquiv_comp h f := TensorAssociativity.Construction.tensorRightTrilinearEquiv_postcomp f h

def TensorAssociativity.Construction.tensorModuleAssocIso (L M N : X.Modules) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M) N ≅ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) :=
  (TensorAssociativity.Construction.tensorLeftTrilinearCorepresentable L M N).uniqueUpToIso (TensorAssociativity.Construction.tensorRightTrilinearCorepresentable L M N)

theorem TensorAssociativity.Construction.tensorClass_assoc (a b c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass a b) c =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass a (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.tensorClass b c) := by
  induction a using Quotient.inductionOn with
  | h L =>
    induction b using Quotient.inductionOn with
    | h M =>
      induction c using Quotient.inductionOn with
      | h N => exact Quotient.sound ⟨TensorAssociativity.Construction.tensorModuleAssocIso L.sheaf M.sheaf N.sheaf⟩

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms
