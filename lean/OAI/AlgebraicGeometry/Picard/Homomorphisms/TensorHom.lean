import OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHom
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves

/-! # Tensor Hom -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorHom

noncomputable section

/-! Currying actual bilinear maps of sheaves into the internal Hom. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} {M N P : X.Modules}

def internalHomEval (M N : X.Modules) (U : X.Opens) :
    Γ(InternalHom.Construction.moduleInternalHom M N, U) →ₗ[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun a :=
    { toFun := a.val.app (.op (Over.mk (𝟙 U)))
      map_add' := fun s t => (a.val.app (.op (Over.mk (𝟙 U)))).hom.map_add s t
      map_smul' := fun r s => a.property (Over.mk (𝟙 U)) r s }
  map_add' a b := by
    ext s
    rfl
  map_smul' r a := by
    ext s
    change X.presheaf.map (𝟙 U).op r •
        (show Γ(N, U) from a.val.app (.op (Over.mk (𝟙 U))) s) =
      r • (show Γ(N, U) from a.val.app (.op (Over.mk (𝟙 U))) s)
    erw [op_id, X.presheaf.map_id, CommRingCat.id_apply]

theorem internalHomEval_naturality (M N : X.Modules) {U V : X.Opens} (f : V ⟶ U)
    (a : Γ(InternalHom.Construction.moduleInternalHom M N, U)) (s : Γ(M, U)) :
    internalHomEval M N V ((InternalHom.Construction.moduleInternalHom M N).presheaf.map f.op a)
        (M.presheaf.map f.op s) =
      N.presheaf.map f.op (internalHomEval M N U a s) := by
  let h : Over.mk f ⟶ Over.mk (𝟙 U) := Over.homMk f
  exact ConcreteCategory.congr_hom (a.val.naturality h.op) s

def sheafBilinearUncurry (f : M ⟶ InternalHom.Construction.moduleInternalHom N P) : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P where
  app U := (internalHomEval N P U).comp (AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.homApp f U)
  naturality {U V} h s t := by
    change P.presheaf.map h.op (internalHomEval N P U (f.app U s) t) =
      internalHomEval N P V (f.app V (M.presheaf.map h.op s)) (N.presheaf.map h.op t)
    rw [← internalHomEval_naturality]
    have he := ConcreteCategory.congr_hom (f.mapPresheaf.naturality h.op) s
    exact congrArg (fun a => internalHomEval N P V a (N.presheaf.map h.op t)) he.symm

def bilinearLocalHom (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (U : X.Opens) (s : Γ(M, U)) :
    (ModuleHomSheaf.Construction.linearHomSubfunctor N P).toFunctor.obj (.op U) :=
  ⟨{ app V := AddCommGrpCat.ofHom
        (b.app V.unop.left (M.presheaf.map V.unop.hom.op s)).toAddMonoidHom
     naturality {V W} f := by
       ext t
       have he := b.naturality f.unop.left (M.presheaf.map V.unop.hom.op s) t
       have hr : M.presheaf.map f.unop.left.op (M.presheaf.map V.unop.hom.op s) =
           M.presheaf.map W.unop.hom.op s := by
         rw [← Functor.map_comp_apply, ← op_comp, Over.w f.unop]
       rw [hr] at he
       exact he.symm },
    fun V r t => (b.app V.left (M.presheaf.map V.hom.op s)).map_smul r t⟩

def sheafBilinearCurry (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) : M ⟶ InternalHom.Construction.moduleInternalHom N P where
  val.app U := ModuleCat.ofHom
    { toFun := bilinearLocalHom b U.unop
      map_add' s t := by
        apply Subtype.ext
        apply NatTrans.ext
        funext V
        apply AddCommGrpCat.ext
        intro x
        change b.app V.unop.left (M.presheaf.map V.unop.hom.op (s + t)) x =
          b.app V.unop.left (M.presheaf.map V.unop.hom.op s) x +
            b.app V.unop.left (M.presheaf.map V.unop.hom.op t) x
        erw [map_add, map_add, LinearMap.add_apply]
      map_smul' r s := by
        apply Subtype.ext
        apply NatTrans.ext
        funext V
        apply AddCommGrpCat.ext
        intro x
        change b.app V.unop.left (M.presheaf.map V.unop.hom.op (r • s)) x =
          X.presheaf.map V.unop.hom.op r •
            b.app V.unop.left (M.presheaf.map V.unop.hom.op s) x
        erw [M.val.map_smul, (b.app V.unop.left).map_smul, LinearMap.smul_apply]
        rfl }
  val.naturality {U V} f := by
    ext s
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    apply AddCommGrpCat.ext
    intro t
    change b.app W.unop.left (M.presheaf.map W.unop.hom.op (M.presheaf.map f s)) t =
      b.app W.unop.left (M.presheaf.map (W.unop.hom ≫ f.unop).op s) t
    rw [op_comp, Functor.map_comp_apply]
    rfl

theorem sheafBilinearUncurry_curry (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) :
    sheafBilinearUncurry (sheafBilinearCurry b) = b := by
  ext U s t
  change b.app U (M.presheaf.map (𝟙 U).op s) t = b.app U s t
  rw [op_id, M.presheaf.map_id, AddCommGrpCat.id_apply]

theorem sheafBilinearCurry_uncurry (f : M ⟶ InternalHom.Construction.moduleInternalHom N P) :
    sheafBilinearCurry (sheafBilinearUncurry f) = f := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro s
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro t
  change internalHomEval N P V.unop.left
    (f.app V.unop.left (M.presheaf.map V.unop.hom.op s)) t =
      (f.app U s).val.app V t
  have he := ConcreteCategory.congr_hom (f.mapPresheaf.naturality V.unop.hom.op) s
  exact congrArg (fun a => internalHomEval N P V.unop.left a t) he

def sheafBilinearCurryEquiv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P ≃ (M ⟶ InternalHom.Construction.moduleInternalHom N P) where
  toFun := sheafBilinearCurry
  invFun := sheafBilinearUncurry
  left_inv := sheafBilinearUncurry_curry
  right_inv := sheafBilinearCurry_uncurry

/-- The tensor–Hom correspondence for actual module sheaves on any scheme. -/
def tensorInternalHomEquiv (M N P : X.Modules) :
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ⟶ P) ≃ (M ⟶ InternalHom.Construction.moduleInternalHom N P) :=
  (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P).trans sheafBilinearCurryEquiv

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorHom
