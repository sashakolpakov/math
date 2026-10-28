import OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafHomSheaf
import OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorFunctors

/-! # Presheaf Tensor Hom -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafTensorHom

noncomputable section

/-! Tensor–Hom for module presheaves with a sheaf as target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}}

local instance presheafTensorHomLocal1 (M : X.PresheafOfModules) (U : X.Opens) :
    Module Γ(X, U) (M.obj (.op U)) := (M.obj (.op U)).isModule

structure PresheafBilinearMap (M N : X.PresheafOfModules) (P : X.Modules) where
  app (U : X.Opens) : M.obj (.op U) →ₗ[Γ(X, U)] N.obj (.op U) →ₗ[Γ(X, U)] Γ(P, U)
  naturality {U V : X.Opens} (f : V ⟶ U) (m : M.obj (.op U)) (n : N.obj (.op U)) :
    P.presheaf.map f.op (app U m n) = app V (M.map f.op m) (N.map f.op n)

variable {M N : X.PresheafOfModules} {P : X.Modules}

@[ext]
theorem PresheafBilinearMap.ext {b c : PresheafBilinearMap M N P}
    (h : ∀ U, b.app U = c.app U) : b = c := by
  cases b
  cases c
  congr
  exact funext h

def presheafHomEval (M : X.PresheafOfModules) (P : X.Modules) (U : X.Opens) :
    Γ(PresheafHomSheaf.Construction.presheafInternalHom M P, U) →ₗ[Γ(X, U)] M.obj (.op U) →ₗ[Γ(X, U)] Γ(P, U) where
  toFun a :=
    { toFun := a.val.app (.op (Over.mk (𝟙 U)))
      map_add' := fun s t => (a.val.app (.op (Over.mk (𝟙 U)))).hom.map_add s t
      map_smul' := fun r s => a.property (Over.mk (𝟙 U)) r s }
  map_add' a b := by ext s; rfl
  map_smul' r a := by
    ext s
    change X.presheaf.map (𝟙 U).op r •
        (show Γ(P, U) from a.val.app (.op (Over.mk (𝟙 U))) s) =
      r • (show Γ(P, U) from a.val.app (.op (Over.mk (𝟙 U))) s)
    erw [op_id, X.presheaf.map_id, CommRingCat.id_apply]

theorem presheafHomEval_naturality (M : X.PresheafOfModules) (P : X.Modules)
    {U V : X.Opens} (f : V ⟶ U) (a : Γ(PresheafHomSheaf.Construction.presheafInternalHom M P, U)) (s : M.obj (.op U)) :
    presheafHomEval M P V ((PresheafHomSheaf.Construction.presheafInternalHom M P).presheaf.map f.op a) (M.map f.op s) =
      P.presheaf.map f.op (presheafHomEval M P U a s) := by
  let h : Over.mk f ⟶ Over.mk (𝟙 U) := Over.homMk f
  exact ConcreteCategory.congr_hom (a.val.naturality h.op) s

def presheafBilinearUncurry (f : M ⟶ (PresheafHomSheaf.Construction.presheafInternalHom N P).val) : PresheafBilinearMap M N P where
  app U := (presheafHomEval N P U).comp (f.app (.op U)).hom
  naturality {U V} h s t := by
    change P.presheaf.map h.op (presheafHomEval N P U (f.app (.op U) s) t) =
      presheafHomEval N P V (f.app (.op V) (M.map h.op s)) (N.map h.op t)
    rw [← presheafHomEval_naturality]
    exact congrArg (fun a => presheafHomEval N P V a (N.map h.op t))
      (PresheafOfModules.naturality_apply f h.op s).symm

def presheafBilinearLocalHom (b : PresheafBilinearMap M N P) (U : X.Opens) (s : M.obj (.op U)) :
    Γ(PresheafHomSheaf.Construction.presheafInternalHom N P, U) :=
  ⟨{ app V := AddCommGrpCat.ofHom (b.app V.unop.left (M.map V.unop.hom.op s)).toAddMonoidHom
     naturality {V W} f := by
       ext t
       have he := b.naturality f.unop.left (M.map V.unop.hom.op s) t
       have hr : M.map f.unop.left.op (M.map V.unop.hom.op s) = M.map W.unop.hom.op s := by
         rw [← M.map_comp_apply, ← op_comp, Over.w f.unop]
       rw [hr] at he
       exact he.symm },
    fun V r t => (b.app V.left (M.map V.hom.op s)).map_smul r t⟩

def presheafBilinearCurry (b : PresheafBilinearMap M N P) : M ⟶ (PresheafHomSheaf.Construction.presheafInternalHom N P).val where
  app U := ModuleCat.ofHom
    { toFun := presheafBilinearLocalHom b U.unop
      map_add' s t := by
        apply Subtype.ext
        apply NatTrans.ext
        funext V
        apply AddCommGrpCat.ext
        intro x
        change b.app V.unop.left (M.map V.unop.hom.op (s + t)) x =
          b.app V.unop.left (M.map V.unop.hom.op s) x + b.app V.unop.left (M.map V.unop.hom.op t) x
        erw [map_add, map_add, LinearMap.add_apply]
      map_smul' r s := by
        apply Subtype.ext
        apply NatTrans.ext
        funext V
        apply AddCommGrpCat.ext
        intro x
        change b.app V.unop.left (M.map V.unop.hom.op (r • s)) x =
          X.presheaf.map V.unop.hom.op r • b.app V.unop.left (M.map V.unop.hom.op s) x
        erw [M.map_smul, (b.app V.unop.left).map_smul, LinearMap.smul_apply]
        rfl }
  naturality {U V} f := by
    ext s
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    apply AddCommGrpCat.ext
    intro t
    change b.app W.unop.left (M.map W.unop.hom.op (M.map f s)) t =
      b.app W.unop.left (M.map (W.unop.hom ≫ f.unop).op s) t
    rw [op_comp, M.map_comp_apply]
    rfl

theorem presheafBilinearUncurry_curry (b : PresheafBilinearMap M N P) :
    presheafBilinearUncurry (presheafBilinearCurry b) = b := by
  ext U s t
  change b.app U (M.map (𝟙 U).op s) t = b.app U s t
  rw [op_id, M.map_id]
  rfl

theorem presheafBilinearCurry_uncurry (f : M ⟶ (PresheafHomSheaf.Construction.presheafInternalHom N P).val) :
    presheafBilinearCurry (presheafBilinearUncurry f) = f := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro t
  change presheafHomEval N P V.unop.left (f.app (.op V.unop.left) (M.map V.unop.hom.op s)) t =
    (f.app U s).val.app V t
  exact congrArg (fun a => presheafHomEval N P V.unop.left a t)
    (PresheafOfModules.naturality_apply f V.unop.hom.op s)

def presheafBilinearCurryEquiv :
    PresheafBilinearMap M N P ≃ (M ⟶ (PresheafHomSheaf.Construction.presheafInternalHom N P).val) where
  toFun := presheafBilinearCurry
  invFun := presheafBilinearUncurry
  left_inv := presheafBilinearUncurry_curry
  right_inv := presheafBilinearCurry_uncurry

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafTensorHom
