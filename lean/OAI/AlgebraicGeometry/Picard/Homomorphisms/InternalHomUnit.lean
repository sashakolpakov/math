import OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorHom

/-! # Internal Hom Unit -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHomUnit

noncomputable section

/-! The internal Hom from the structure sheaf is the target sheaf itself. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} (N : X.Modules)

def internalHomUnitEval : InternalHom.Construction.moduleInternalHom (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) N ⟶ N where
  val.app U := ModuleCat.ofHom ((TensorHom.Construction.internalHomEval (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) N U.unop).flip
    (1 : Γ(X, U.unop)))
  val.naturality {U V} f := by
    ext a
    have he := TensorHom.Construction.internalHomEval_naturality (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) N f.unop a
      (1 : Γ(X, U.unop))
    change TensorHom.Construction.internalHomEval (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) N V.unop
        ((InternalHom.Construction.moduleInternalHom (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) N).presheaf.map f a) (1 : Γ(X, V.unop)) = _
    have h1 : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).presheaf.map f.unop.op (1 : Γ(X, U.unop)) =
        (1 : Γ(X, V.unop)) := (X.presheaf.map f.unop.op).hom.map_one
    rw [h1] at he
    exact he

def moduleUnitBilinear : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap N (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) N where
  app U := (LinearMap.lsmul Γ(X, U) Γ(N, U)).flip
  naturality {_U _V} f s r := N.val.map_smul f.op r s

def internalHomUnitInv : N ⟶ InternalHom.Construction.moduleInternalHom (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) N :=
  TensorHom.Construction.sheafBilinearCurry (moduleUnitBilinear N)

theorem internalHomUnitInv_eval : internalHomUnitInv N ≫ internalHomUnitEval N = 𝟙 N := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro s
  change (1 : Γ(X, U)) • N.presheaf.map (𝟙 U).op s = s
  rw [op_id, N.presheaf.map_id, AddCommGrpCat.id_apply, one_smul]

theorem internalHomUnitEval_inv : internalHomUnitEval N ≫ internalHomUnitInv N = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro a
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro r
  change Γ(X, V.unop.left) at r
  change r • N.presheaf.map V.unop.hom.op
      (TensorHom.Construction.internalHomEval (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) N U a (1 : Γ(X, U))) =
    a.val.app V r
  have hn := TensorHom.Construction.internalHomEval_naturality (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) N V.unop.hom a
    (1 : Γ(X, U))
  have h1 : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).presheaf.map V.unop.hom.op (1 : Γ(X, U)) =
      (1 : Γ(X, V.unop.left)) := (X.presheaf.map V.unop.hom.op).hom.map_one
  rw [h1] at hn
  rw [← hn]
  change r • (show Γ(N, V.unop.left) from a.val.app V (1 : Γ(X, V.unop.left))) =
    a.val.app V r
  have he := a.property V.unop r (1 : Γ(X, V.unop.left))
  exact he.symm.trans (congrArg (fun t : Γ(X, V.unop.left) => a.val.app V t) (mul_one r))

def internalHomUnitIso : InternalHom.Construction.moduleInternalHom (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) N ≅ N where
  hom := internalHomUnitEval N
  inv := internalHomUnitInv N
  hom_inv_id := internalHomUnitEval_inv N
  inv_hom_id := internalHomUnitInv_eval N

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHomUnit
