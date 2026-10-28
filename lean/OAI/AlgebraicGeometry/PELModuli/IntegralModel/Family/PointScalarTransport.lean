import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointBaseChange

/-! # Point Scalar Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointScalarTransport

noncomputable section

/-! Transport on a pulled-back family agrees, under its actual first
projection, with transport through the canonical flattened comparison. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace FamilyPointTransport
variable {S V T : Scheme.{0}} (A : Over S) (v : V ⟶ S)

theorem pullbackComp_inv_fst (f : T ⟶ V) :
    ((Over.pullbackComp f v).inv.app A).left ≫ pullback.fst A.hom (f ≫ v) =
      pullback.fst ((Over.pullback v).obj A).hom f ≫ pullback.fst A.hom v :=
  (((Over.forget T).mapIso ((Over.pullbackComp f v).app A)).inv_comp_eq).mpr
    (AbelianModuli.HilbertConstruction.Pullback.Comparisons.pullbackComp_hom_fst_fst A v f).symm

theorem liftPoint_flatten (f : T ⟶ V)
    (x : T ⟶ ((Over.pullback v).obj A).left)
    (hx : x ≫ ((Over.pullback v).obj A).hom = f) :
    PointBaseChange.FamilyPointTransport.liftPoint ((Over.pullback v).obj A) f x hx ≫ ((Over.pullbackComp f v).inv.app A).left =
      PointBaseChange.FamilyPointTransport.liftPoint A (f ≫ v) (x ≫ pullback.fst A.hom v)
        (by rw [Category.assoc, pullback.condition, ← Category.assoc]; exact congrArg (fun k => k ≫ v) hx) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackComp_inv_fst, ← Category.assoc, PointBaseChange.FamilyPointTransport.liftPoint_fst, PointBaseChange.FamilyPointTransport.liftPoint_fst]
  · change (PointBaseChange.FamilyPointTransport.liftPoint ((Over.pullback v).obj A) f x hx ≫
        ((Over.pullbackComp f v).inv.app A).left) ≫ pullback.snd A.hom (f ≫ v) = _
    have hw : ((Over.pullbackComp f v).inv.app A).left ≫ pullback.snd A.hom (f ≫ v) =
        pullback.snd ((Over.pullback v).obj A).hom f := ((Over.pullbackComp f v).inv.app A).w
    rw [Category.assoc, hw, PointBaseChange.FamilyPointTransport.liftPoint_snd, PointBaseChange.FamilyPointTransport.liftPoint_snd]

def flattenedTransportIso (f g : T ⟶ V)
    (e : (Over.pullback f).obj ((Over.pullback v).obj A) ≅
      (Over.pullback g).obj ((Over.pullback v).obj A)) :
    (Over.pullback (f ≫ v)).obj A ≅ (Over.pullback (g ≫ v)).obj A :=
  (Over.pullbackComp f v).app A ≪≫ e ≪≫ ((Over.pullbackComp g v).app A).symm

theorem transport_scalar_fst (f g : T ⟶ V)
    (e : (Over.pullback f).obj ((Over.pullback v).obj A) ≅
      (Over.pullback g).obj ((Over.pullback v).obj A))
    (x : T ⟶ ((Over.pullback v).obj A).left)
    (hx : x ≫ ((Over.pullback v).obj A).hom = f) :
    PointBaseChange.FamilyPointTransport.transport ((Over.pullback v).obj A) f g e x hx ≫ pullback.fst A.hom v =
      PointBaseChange.FamilyPointTransport.transport A (f ≫ v) (g ≫ v) (flattenedTransportIso A v f g e)
        (x ≫ pullback.fst A.hom v)
        (by rw [Category.assoc, pullback.condition, ← Category.assoc]; exact congrArg (fun k => k ≫ v) hx) := by
  have hp := liftPoint_flatten A v f x hx
  change (PointBaseChange.FamilyPointTransport.liftPoint ((Over.pullback v).obj A) f x hx ≫ e.hom.left ≫
      pullback.fst ((Over.pullback v).obj A).hom g) ≫ pullback.fst A.hom v =
    PointBaseChange.FamilyPointTransport.liftPoint A (f ≫ v) (x ≫ pullback.fst A.hom v) _ ≫
      (((Over.pullbackComp f v).hom.app A).left ≫ e.hom.left ≫
        ((Over.pullbackComp g v).inv.app A).left) ≫ pullback.fst A.hom (g ≫ v)
  rw [← hp]
  simp only [Category.assoc]
  have hi : ((Over.pullbackComp f v).inv.app A).left ≫
      ((Over.pullbackComp f v).hom.app A).left = 𝟙 _ :=
    congrArg Over.Hom.left (((Over.pullbackComp f v).app A).inv_hom_id)
  rw [← Category.assoc ((Over.pullbackComp f v).inv.app A).left
    ((Over.pullbackComp f v).hom.app A).left,
    hi, Category.id_comp, pullbackComp_inv_fst]

end FamilyPointTransport

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointScalarTransport
