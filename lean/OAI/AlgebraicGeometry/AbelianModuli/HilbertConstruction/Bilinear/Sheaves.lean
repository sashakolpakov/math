import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers

/-! # Sheaves -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves

noncomputable section

/-! Bilinear maps of module sheaves and the universal property of their actual tensor product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable {X : Scheme.{u}}

/-- Bilinear maps on sections compatible with restriction to smaller opens. -/
structure SheafBilinearMap (M N P : X.Modules) where
  app (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) →ₗ[Γ(X, U)] Γ(P, U)
  naturality {U V : X.Opens} (h : V ⟶ U) (x : Γ(M, U)) (y : Γ(N, U)) :
    P.presheaf.map h.op (app U x y) =
      app V (M.presheaf.map h.op x) (N.presheaf.map h.op y)

namespace SheafBilinearMap

variable {M M' N N' P Q R : X.Modules}

@[ext]
theorem ext {β γ : SheafBilinearMap M N P} (h : ∀ U, β.app U = γ.app U) : β = γ := by
  cases β
  cases γ
  congr
  exact funext h

/-- Postcompose a bilinear map by a morphism of module sheaves. -/
def postcomp (β : SheafBilinearMap M N P) (f : P ⟶ Q) : SheafBilinearMap M N Q where
  app U := (β.app U).compr₂ (Tensor.Powers.SheafMultilinearMap.homApp f U)
  naturality {U V} h x y :=
    (ConcreteCategory.congr_hom (f.mapPresheaf.naturality h.op) (β.app U x y)).symm.trans
      (congrArg (fun z => f.app V z) (β.naturality h x y))

/-- Precompose the two arguments independently. -/
def precomp (β : SheafBilinearMap M N P) (f : M' ⟶ M) (g : N' ⟶ N) :
    SheafBilinearMap M' N' P where
  app U := (β.app U).compl₁₂ (Tensor.Powers.SheafMultilinearMap.homApp f U) (Tensor.Powers.SheafMultilinearMap.homApp g U)
  naturality {U V} h x y :=
    (β.naturality h (f.app U x) (g.app U y)).trans
      (congrArg₂ (fun a b => β.app V a b)
        (ConcreteCategory.congr_hom (f.mapPresheaf.naturality h.op) x).symm
        (ConcreteCategory.congr_hom (g.mapPresheaf.naturality h.op) y).symm)

@[simp]
theorem postcomp_id (β : SheafBilinearMap M N P) : β.postcomp (𝟙 P) = β := by
  ext U x y
  rfl

theorem postcomp_comp (β : SheafBilinearMap M N P) (f : P ⟶ Q) (g : Q ⟶ R) :
    β.postcomp (f ≫ g) = (β.postcomp f).postcomp g := by
  ext U x y
  rfl

@[simp]
theorem precomp_id (β : SheafBilinearMap M N P) : β.precomp (𝟙 M) (𝟙 N) = β := by
  ext U x y
  rfl

theorem precomp_postcomp (β : SheafBilinearMap M N P) (f : M' ⟶ M) (g : N' ⟶ N)
    (h : P ⟶ Q) :
    (β.postcomp h).precomp f g = (β.precomp f g).postcomp h := by
  ext U x y
  rfl

/-- A map out of the tensor presheaf gives its bilinear formula on sections. -/
def ofTensorPresheafHom
    (f : PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val ⟶ P.val) :
    SheafBilinearMap M N P where
  app U := TensorProduct.curry (f.app (.op U)).hom
  naturality h x y := (PresheafOfModules.naturality_apply f h.op (x ⊗ₜ y)).symm

/-- A bilinear section formula defines a map out of the tensor presheaf. -/
def toTensorPresheafHom (β : SheafBilinearMap M N P) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val ⟶ P.val where
  app U := (ModuleCat.ofHom (TensorProduct.lift (β.app U.unop)) :
    ModuleCat.of Γ(X, U.unop) (Γ(M, U.unop) ⊗[Γ(X, U.unop)] Γ(N, U.unop)) ⟶
      ModuleCat.of Γ(X, U.unop) Γ(P, U.unop))
  naturality {_U _V} h := ModuleCat.MonoidalCategory.tensor_ext
    (fun x y => (β.naturality h.unop x y).symm)

/-- The tensor presheaf has exactly the prescribed natural bilinear maps. -/
def tensorPresheafHomEquiv (M N P : X.Modules) :
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val ⟶ P.val) ≃
      SheafBilinearMap M N P where
  toFun := ofTensorPresheafHom
  invFun := toTensorPresheafHom
  left_inv f := by
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    rfl
  right_inv β := by
    ext U x y
    rfl

/-- The actual sheaf tensor product represents natural bilinear maps. -/
def tensorHomEquiv (M N P : X.Modules) :
    (Tensor.ProductSheaf.tensorModule M N ⟶ P) ≃ SheafBilinearMap M N P :=
  (Tensor.ProductSheaf.tensorModuleHomEquiv M N P).trans (tensorPresheafHomEquiv M N P)

/-- Varying the output sheaf gives the functor represented by the tensor sheaf. -/
def outputFunctor (M N : X.Modules) : X.Modules ⥤ Type u where
  obj P := SheafBilinearMap M N P
  map {P Q} f := TypeCat.ofHom (fun β : SheafBilinearMap M N P => β.postcomp f)
  map_id P := by
    apply ConcreteCategory.ext_apply
    intro β
    exact β.postcomp_id
  map_comp f g := by
    apply ConcreteCategory.ext_apply
    exact fun β => β.postcomp_comp f g

/-- The tensor-to-bilinear equivalence is natural in the output sheaf. -/
theorem tensorHomEquiv_postcomp (f : Tensor.ProductSheaf.tensorModule M N ⟶ P) (h : P ⟶ Q) :
    tensorHomEquiv M N Q (f ≫ h) = (tensorHomEquiv M N P f).postcomp h := by
  have he : Tensor.ProductSheaf.tensorModuleHomEquiv M N Q (f ≫ h) =
      Tensor.ProductSheaf.tensorModuleHomEquiv M N P f ≫ h.val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_right f h
  change ofTensorPresheafHom (Tensor.ProductSheaf.tensorModuleHomEquiv M N Q (f ≫ h)) = _
  rw [he]
  ext U x y
  rfl

/-- The tensor sheaf corepresents the functor of natural bilinear maps. -/
def corepresentable (M N : X.Modules) :
    (outputFunctor M N).CorepresentableBy (Tensor.ProductSheaf.tensorModule M N) where
  homEquiv := tensorHomEquiv M N _
  homEquiv_comp g f := tensorHomEquiv_postcomp f g

end SheafBilinearMap

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves
