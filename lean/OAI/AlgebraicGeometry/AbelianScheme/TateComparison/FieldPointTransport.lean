import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldGroupPoints

/-! # Field Point Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport

noncomputable section

/-! Exact point transport and endomorphism conjugation along a base change,
with an explicitly specified common base point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S S' T : Scheme.{u}} (p : S' ⟶ S) (c : T ⟶ S') (b : T ⟶ S)
  (h : c ≫ p = b)

def pointBaseChangeSourceIso : (Over.map p).obj (Over.mk c) ≅ Over.mk b :=
  Over.isoMk (Iso.refl _) (by simpa using h.symm)

def pointBaseChangeEquiv (X : Over S) :
    (Over.mk c ⟶ (Over.pullback p).obj X) ≃ (Over.mk b ⟶ X) :=
  ((Over.mapPullbackAdj p).homEquiv (Over.mk c) X).symm.trans
    ((pointBaseChangeSourceIso p c b h).homCongr (Iso.refl X))

@[simp]
theorem pointBaseChangeEquiv_left (X : Over S)
    (x : Over.mk c ⟶ (Over.pullback p).obj X) :
    (pointBaseChangeEquiv p c b h X x).left = x.left ≫ pullback.fst X.hom p := by
  change 𝟙 T ≫ (x.left ≫ pullback.fst X.hom p) ≫ 𝟙 X.left = _
  simp only [Category.id_comp, Category.comp_id]

def pointBaseChangeMulEquiv (A : Over S) [GrpObj A] :
    (Over.mk c ⟶ (Over.pullback p).obj A) ≃* (Over.mk b ⟶ A) :=
  (PELModuli.IntegralModel.Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv A p (Over.mk c)).trans
    (PELModuli.IntegralModel.FieldGroupPoints.homDomainMulEquiv (pointBaseChangeSourceIso p c b h).symm A)

@[simp]
theorem pointBaseChangeMulEquiv_left (A : Over S) [GrpObj A]
    (x : Over.mk c ⟶ (Over.pullback p).obj A) :
    (pointBaseChangeMulEquiv p c b h A x).left = x.left ≫ pullback.fst A.hom p := by
  change 𝟙 T ≫ (x.left ≫ pullback.fst A.hom p) = _
  exact Category.id_comp _

theorem pointBaseChange_comp {X : Over S} (A : Over S) [GrpObj A]
    (f : X ⟶ A) (x : Over.mk c ⟶ (Over.pullback p).obj X) :
    pointBaseChangeMulEquiv p c b h A (x ≫ (Over.pullback p).map f) =
      pointBaseChangeEquiv p c b h X x ≫ f := by
  apply Over.OverMorphism.ext
  simp only [pointBaseChangeMulEquiv_left, pointBaseChangeEquiv_left, Over.comp_left,
    Over.pullback_map_left, Category.assoc, pullback.lift_fst]

def pointBaseChangeEnd (A : Over S) [GrpObj A]
    (φ : (Over.pullback p).obj A ⟶ (Over.pullback p).obj A) [IsMonHom φ] :
    Additive (Over.mk b ⟶ A) →+ Additive (Over.mk b ⟶ A) where
  toFun z := Additive.ofMul (pointBaseChangeMulEquiv p c b h A
    ((pointBaseChangeMulEquiv p c b h A).symm z.toMul ≫ φ))
  map_zero' := by
    change Additive.ofMul (pointBaseChangeMulEquiv p c b h A
      ((pointBaseChangeMulEquiv p c b h A).symm 1 ≫ φ)) = Additive.ofMul 1
    rw [map_one, MonObj.one_comp, map_one]
  map_add' x y := by
    change Additive.ofMul (pointBaseChangeMulEquiv p c b h A
      ((pointBaseChangeMulEquiv p c b h A).symm (x.toMul * y.toMul) ≫ φ)) =
      Additive.ofMul (_ * _)
    rw [map_mul, MonObj.mul_comp, map_mul]
    rfl

theorem pointBaseChangeEnd_apply (A : Over S) [GrpObj A]
    (φ : (Over.pullback p).obj A ⟶ (Over.pullback p).obj A) [IsMonHom φ]
    (x : Over.mk c ⟶ (Over.pullback p).obj A) :
    pointBaseChangeEnd p c b h A φ (Additive.ofMul (pointBaseChangeMulEquiv p c b h A x)) =
      Additive.ofMul (pointBaseChangeMulEquiv p c b h A (x ≫ φ)) := by
  change Additive.ofMul (pointBaseChangeMulEquiv p c b h A
    ((pointBaseChangeMulEquiv p c b h A).symm (pointBaseChangeMulEquiv p c b h A x) ≫ φ)) = _
  rw [MulEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport
