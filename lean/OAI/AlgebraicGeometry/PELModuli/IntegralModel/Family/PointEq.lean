import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.PointsBaseChange

/-! # Point Eq -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointEq.FamilyPointTransport

noncomputable section

section

/-! Actual point transport through a group-family comparison is a
group isomorphism on each fiber's scheme-valued points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def precomposeMulEquiv {S : Scheme.{0}} (A : Over S) [GrpObj A]
    {T W : Over S} (d : T ≅ W) : (W ⟶ A) ≃* (T ⟶ A) where
  toFun x := d.hom ≫ x
  invFun x := d.inv ≫ x
  left_inv x := by simp only [← Category.assoc, d.inv_hom_id, Category.id_comp]
  right_inv x := by simp only [← Category.assoc, d.hom_inv_id, Category.id_comp]
  map_mul' x y := MonObj.comp_mul d.hom x y

def sectionPointEquiv {S T : Scheme.{0}} (A : Over S) [GrpObj A] (f : T ⟶ S) :
    (Over.mk f ⟶ A) ≃* (Over.mk (𝟙 T) ⟶ (Over.pullback f).obj A) :=
  (precomposeMulEquiv A (Over.isoMk (Iso.refl T) (show 𝟙 T ≫ f = (𝟙 T) ≫ f from rfl))).trans
    (Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv A f (Over.mk (𝟙 T))).symm

theorem sectionPointEquiv_symm_left {S T : Scheme.{0}} (A : Over S) [GrpObj A] (f : T ⟶ S)
    (x : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj A) :
    ((sectionPointEquiv A f).symm x).left = x.left ≫ pullback.fst A.hom f := by
  change 𝟙 T ≫ (x.left ≫ pullback.fst A.hom f) = _
  exact Category.id_comp _

theorem sectionPointEquiv_left {S T : Scheme.{0}} (A : Over S) [GrpObj A] (f : T ⟶ S)
    (x : Over.mk f ⟶ A) : (sectionPointEquiv A f x).left = PointBaseChange.FamilyPointTransport.liftPoint A f x.left x.w := by
  apply pullback.hom_ext
  · have h := congrArg Over.Hom.left ((sectionPointEquiv A f).symm_apply_apply x)
    rw [sectionPointEquiv_symm_left] at h
    exact h.trans (PointBaseChange.FamilyPointTransport.liftPoint_fst A f x.left x.w).symm
  · exact (sectionPointEquiv A f x).w.trans (PointBaseChange.FamilyPointTransport.liftPoint_snd A f x.left x.w).symm

def pointTransportMulEquiv {S T : Scheme.{0}} (A : Over S) [GrpObj A] (f g : T ⟶ S)
    (e : (Over.pullback f).obj A ≅ (Over.pullback g).obj A) [IsMonHom e.hom] :
    (Over.mk f ⟶ A) ≃* (Over.mk g ⟶ A) :=
  (sectionPointEquiv A f).trans
    ((Hom.mulEquivCongrRight e (Over.mk (𝟙 T))).trans (sectionPointEquiv A g).symm)

theorem pointTransportMulEquiv_left {S T : Scheme.{0}} (A : Over S) [GrpObj A] (f g : T ⟶ S)
    (e : (Over.pullback f).obj A ≅ (Over.pullback g).obj A) [IsMonHom e.hom]
    (x : Over.mk f ⟶ A) :
    (pointTransportMulEquiv A f g e x).left = PointBaseChange.FamilyPointTransport.transport A f g e x.left x.w := by
  change ((sectionPointEquiv A g).symm (sectionPointEquiv A f x ≫ e.hom)).left = _
  rw [sectionPointEquiv_symm_left]
  change ((sectionPointEquiv A f x).left ≫ e.hom.left) ≫ pullback.fst A.hom g = _
  rw [sectionPointEquiv_left, Category.assoc]
  rfl

end

section

/-! Group-operation formulas for the previously constructed actual
scheme-point transport maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S T : Scheme.{0}} (A : Over S) [GrpObj A] (f g : T ⟶ S)
    (e : (Over.pullback f).obj A ≅ (Over.pullback g).obj A) [IsMonHom e.hom]

def transportPoint (x : Over.mk f ⟶ A) : Over.mk g ⟶ A :=
  Over.homMk (PointBaseChange.FamilyPointTransport.transport A f g e x.left x.w) (PointBaseChange.FamilyPointTransport.transport_base A f g e x.left x.w)

theorem transportPoint_eq (x : Over.mk f ⟶ A) :
    transportPoint A f g e x = pointTransportMulEquiv A f g e x :=
  Over.OverMorphism.ext (pointTransportMulEquiv_left A f g e x).symm

theorem transportPoint_one : transportPoint A f g e 1 = 1 :=
  (transportPoint_eq A f g e 1).trans (map_one (pointTransportMulEquiv A f g e))

theorem transportPoint_mul (x y : Over.mk f ⟶ A) :
    transportPoint A f g e (x * y) = transportPoint A f g e x * transportPoint A f g e y := by
  simp only [transportPoint_eq, map_mul]

theorem transportPoint_inv (x : Over.mk f ⟶ A) :
    transportPoint A f g e x⁻¹ = (transportPoint A f g e x)⁻¹ := by
  simp only [transportPoint_eq, map_inv]

theorem transport_inv (x : Over.mk f ⟶ A) :
    PointBaseChange.FamilyPointTransport.transport A f g e (x.left ≫ (GrpObj.inv : A ⟶ A).left)
      (by rw [Category.assoc]; exact (congrArg (fun m => x.left ≫ m) (GrpObj.inv : A ⟶ A).w).trans x.w) =
      PointBaseChange.FamilyPointTransport.transport A f g e x.left x.w ≫ (GrpObj.inv : A ⟶ A).left :=
  congrArg Over.Hom.left (transportPoint_inv A f g e x)

end

/-! Multiplication on scheme-valued fiber points, expressed through the
actual relative-product projection maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem over_pair_mul_left {S T : Scheme.{0}} (A : Over S) [GrpObj A]
    (f : T ⟶ S) (p : Over.mk f ⟶ A ⊗ A) :
    ((p ≫ fst A A) * (p ≫ snd A A)).left = p.left ≫ (MonObj.mul : A ⊗ A ⟶ A).left := by
  exact congrArg Over.Hom.left ((MonObj.comp_mul p (fst A A) (snd A A)).symm.trans
    (congrArg (fun h => p ≫ h) (MonObj.mul_eq_mul (M := A)).symm))

theorem over_mul_left {S T : Scheme.{0}} (A : Over S) [GrpObj A]
    (f : T ⟶ S) (x y : Over.mk f ⟶ A) :
    (x * y).left = (pullback.lift x.left y.left (x.w.trans y.w.symm)) ≫
      (MonObj.mul : A ⊗ A ⟶ A).left := rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointEq.FamilyPointTransport
