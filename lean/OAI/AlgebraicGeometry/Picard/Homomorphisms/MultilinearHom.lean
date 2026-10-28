import OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorHom
import OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorPowerSheaf
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! # Multilinear Hom -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.MultilinearHom

noncomputable section

/-! Currying the last variable of an actual sheaf-multilinear map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} {L P : X.Modules} {n : ℕ}

theorem multilinear_curryRight_naturality (b : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L (n + 1) P)
    {U V : X.Opens} (f : V ⟶ U) (s : Fin n → Γ(L, U)) (t : Γ(L, U)) :
    P.presheaf.map f.op ((b.app U).curryRight s t) =
      (b.app V).curryRight (fun i => L.presheaf.map f.op (s i)) (L.presheaf.map f.op t) := by
  change P.presheaf.map f.op (b.app U (Fin.snoc s t)) =
    b.app V (Fin.snoc (fun i => L.presheaf.map f.op (s i)) (L.presheaf.map f.op t))
  rw [b.naturality]
  exact congrArg (b.app V) (Fin.comp_snoc (fun t => L.presheaf.map f.op t) s t)

def multilinearLocalHom (b : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L (n + 1) P)
    (U : X.Opens) (s : Fin n → Γ(L, U)) : Γ(InternalHom.Construction.moduleInternalHom L P, U) :=
  ⟨{ app V := AddCommGrpCat.ofHom
        ((b.app V.unop.left).curryRight (fun i => L.presheaf.map V.unop.hom.op (s i))).toAddMonoidHom
     naturality {V W} f := by
       ext t
       have he := multilinear_curryRight_naturality b f.unop.left
         (fun i => L.presheaf.map V.unop.hom.op (s i)) t
       have hs : (fun i => L.presheaf.map f.unop.left.op (L.presheaf.map V.unop.hom.op (s i))) =
           (fun i => L.presheaf.map W.unop.hom.op (s i)) := by
         funext i
         rw [← Functor.map_comp_apply, ← op_comp, Over.w f.unop]
       rw [hs] at he
       exact he.symm },
    fun V r t => ((b.app V.left).curryRight
      (fun i => L.presheaf.map V.hom.op (s i))).map_smul r t⟩

def sheafMultilinearCurryRight (b : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L (n + 1) P) :
    AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L n (InternalHom.Construction.moduleInternalHom L P) where
  app U :=
    { toFun := multilinearLocalHom b U
      map_update_add' s i x y := by
        apply Subtype.ext
        apply NatTrans.ext
        funext V
        apply AddCommGrpCat.ext
        intro t
        let c := (b.app V.unop.left).curryRight
        have he := (congrArg c (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerVectorMap_update L V.unop.hom.op s i (x + y))).trans
          ((congrArg (fun z => c (Function.update (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerVectorMap L V.unop.hom.op s) i z))
            ((L.val.map V.unop.hom.op).hom.map_add x y)).trans
            ((c.map_update_add (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerVectorMap L V.unop.hom.op s) i _ _).trans
              (congrArg₂ (fun a b => c a + c b)
                (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerVectorMap_update L V.unop.hom.op s i x).symm
                (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerVectorMap_update L V.unop.hom.op s i y).symm)))
        exact congrArg (fun z : Γ(L, V.unop.left) →ₗ[Γ(X, V.unop.left)] Γ(P, V.unop.left) => z t) he
      map_update_smul' s i r x := by
        apply Subtype.ext
        apply NatTrans.ext
        funext V
        apply AddCommGrpCat.ext
        intro t
        let c := (b.app V.unop.left).curryRight
        have he := (congrArg c (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerVectorMap_update L V.unop.hom.op s i (r • x))).trans
          ((congrArg (fun z => c (Function.update (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerVectorMap L V.unop.hom.op s) i z))
            (L.val.map_smul V.unop.hom.op r x)).trans
            ((c.map_update_smul (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerVectorMap L V.unop.hom.op s) i
              (X.presheaf.map V.unop.hom.op r) _).trans
              (congrArg (fun a => (X.presheaf.map V.unop.hom.op r) • c a)
                (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerVectorMap_update L V.unop.hom.op s i x).symm)))
        exact congrArg (fun z : Γ(L, V.unop.left) →ₗ[Γ(X, V.unop.left)] Γ(P, V.unop.left) => z t) he }
  naturality {U V} f s := by
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    apply AddCommGrpCat.ext
    intro t
    change (b.app W.unop.left).curryRight
        (fun i => L.presheaf.map (W.unop.hom ≫ f).op (s i)) t =
      (b.app W.unop.left).curryRight
        (fun i => L.presheaf.map W.unop.hom.op (L.presheaf.map f.op (s i))) t
    simp only [op_comp, Functor.map_comp_apply]

def sheafMultilinearUncurryRight (b : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L n (InternalHom.Construction.moduleInternalHom L P)) :
    AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L (n + 1) P where
  app U := ((TensorHom.Construction.internalHomEval L P U).compMultilinearMap (b.app U)).uncurryRight
  naturality {U V} f s := by
    change P.presheaf.map f.op (TensorHom.Construction.internalHomEval L P U (b.app U (Fin.init s)) (s (Fin.last n))) =
      TensorHom.Construction.internalHomEval L P V (b.app V (fun i => L.presheaf.map f.op (s i.castSucc)))
        (L.presheaf.map f.op (s (Fin.last n)))
    rw [← TensorHom.Construction.internalHomEval_naturality, b.naturality]
    rfl

theorem sheafMultilinear_uncurry_curry (b : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L (n + 1) P) :
    sheafMultilinearUncurryRight (sheafMultilinearCurryRight b) = b := by
  ext U s
  change (b.app U).curryRight (fun i => L.presheaf.map (𝟙 U).op (s i.castSucc)) (s (Fin.last n)) =
    b.app U s
  simp only [op_id, L.presheaf.map_id, AddCommGrpCat.id_apply]
  exact congrArg (fun b : MultilinearMap Γ(X, U) (fun _ : Fin (n + 1) => Γ(L, U)) Γ(P, U) => b s)
    (b.app U).uncurry_curryRight

theorem sheafMultilinear_curry_uncurry (b : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L n (InternalHom.Construction.moduleInternalHom L P)) :
    sheafMultilinearCurryRight (sheafMultilinearUncurryRight b) = b := by
  ext U s
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro t
  change Γ(L, V.unop.left) at t
  change TensorHom.Construction.internalHomEval L P V.unop.left
      (b.app V.unop.left (Fin.init (Fin.snoc (α := fun _ : Fin (n + 1) => Γ(L, V.unop.left))
        (fun i : Fin n => L.presheaf.map V.unop.hom.op (s i)) t)))
      ((Fin.snoc (α := fun _ : Fin (n + 1) => Γ(L, V.unop.left))
        (fun i : Fin n => L.presheaf.map V.unop.hom.op (s i)) t) (Fin.last n)) =
    (b.app U s).val.app V t
  rw [Fin.init_snoc, Fin.snoc_last]
  exact congrArg (fun a => TensorHom.Construction.internalHomEval L P V.unop.left a t) (b.naturality V.unop.hom s).symm

def sheafMultilinearCurryRightEquiv :
    AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L (n + 1) P ≃ AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L n (InternalHom.Construction.moduleInternalHom L P) where
  toFun := sheafMultilinearCurryRight
  invFun := sheafMultilinearUncurryRight
  left_inv := sheafMultilinear_uncurry_curry
  right_inv := sheafMultilinear_curry_uncurry

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.MultilinearHom
