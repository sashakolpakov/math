import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Pair -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair

noncomputable section

/-!
# The kernel-pair torsor isomorphism for PoincareBundle

Two points of a group-scheme quotient have the same image exactly when
their difference lies in its scheme-theoretic kernel. This is an actual
isomorphism between the corresponding fiber product and the product
with the kernel, including for nonreduced kernels.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
  {A B : C} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

/-- The kernel element measuring the difference between two points in one fiber. -/
def difference : pullback f f ⟶ Scheme.kernelObject f :=
  (Scheme.kernelPointsEquiv f (pullback f f)).symm
    ⟨(pullback.fst f f)⁻¹ * pullback.snd f f, by
      change ((pullback.fst f f)⁻¹ * pullback.snd f f) ≫ f = 1
      rw [MonObj.mul_comp, GrpObj.inv_comp, pullback.condition, inv_mul_cancel]⟩

/-- The difference map has its expected inclusion in the original group. -/
theorem difference_comp_inclusion :
    difference f ≫ Scheme.kernelInclusion f =
      (pullback.fst f f)⁻¹ * pullback.snd f f :=
  pullback.lift_fst _ _ _

/-- A point and a kernel element give two points of the same fiber. -/
def kernelPairHom : A ⊗ Scheme.kernelObject f ⟶ pullback f f :=
  pullback.lift (fst _ _) ((fst _ _) * (snd _ _ ≫ Scheme.kernelInclusion f)) (by
    rw [MonObj.mul_comp, Category.assoc, Scheme.kernelInclusion_comp,
      MonObj.comp_one, mul_one])

@[simp]
theorem kernelPairHom_fst : kernelPairHom f ≫ pullback.fst f f = fst _ _ :=
  pullback.lift_fst _ _ _

@[simp]
theorem kernelPairHom_snd : kernelPairHom f ≫ pullback.snd f f =
    (fst _ _) * (snd _ _ ≫ Scheme.kernelInclusion f) :=
  pullback.lift_snd _ _ _

/-- Recover the first point and their difference. -/
def kernelPairInv : pullback f f ⟶ A ⊗ Scheme.kernelObject f :=
  lift (pullback.fst f f) (difference f)

@[simp]
theorem kernelPairInv_fst : kernelPairInv f ≫ fst _ _ = pullback.fst f f :=
  lift_fst _ _

@[simp]
theorem kernelPairInv_snd : kernelPairInv f ≫ snd _ _ = difference f :=
  lift_snd _ _

/-- The fiber relation is canonically the action relation of the full kernel scheme. -/
def kernelPairIso : A ⊗ Scheme.kernelObject f ≅ pullback f f where
  hom := kernelPairHom f
  inv := kernelPairInv f
  hom_inv_id := by
    apply hom_ext
    · simp only [Category.assoc, kernelPairInv_fst, kernelPairHom_fst, Category.id_comp]
    · apply (cancel_mono (Scheme.kernelInclusion f)).mp
      simp only [Category.assoc, kernelPairInv_snd, difference_comp_inclusion,
        MonObj.comp_mul, GrpObj.comp_inv, kernelPairHom_fst, kernelPairHom_snd,
        Category.id_comp, inv_mul_cancel_left]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, kernelPairHom_fst, kernelPairInv_fst, Category.id_comp]
    · rw [Category.assoc, kernelPairHom_snd, MonObj.comp_mul,
        kernelPairInv_fst, ← Category.assoc, kernelPairInv_snd,
        difference_comp_inclusion, Category.id_comp, mul_inv_cancel_left]

attribute [local instance] Scheme.kernelGroup

/-- The kernel-valued difference of any two equal-image test points. -/
def pointDifference {T : C} (x y : T ⟶ A) (h : x ≫ f = y ≫ f) :
    T ⟶ Scheme.kernelObject f :=
  pullback.lift x y h ≫ difference f

@[simp]
theorem pointDifference_comp_inclusion {T : C} (x y : T ⟶ A) (h : x ≫ f = y ≫ f) :
    pointDifference f x y h ≫ Scheme.kernelInclusion f = x⁻¹ * y := by
  rw [pointDifference, Category.assoc, difference_comp_inclusion,
    MonObj.comp_mul, GrpObj.comp_inv, pullback.lift_fst, pullback.lift_snd]

/-- The difference cocycle is the group law on the scheme-theoretic kernel. -/
theorem pointDifference_cocycle {T : C} (x y z : T ⟶ A)
    (hxy : x ≫ f = y ≫ f) (hyz : y ≫ f = z ≫ f) :
    pointDifference f x z (hxy.trans hyz) =
      pointDifference f x y hxy * pointDifference f y z hyz := by
  apply (cancel_mono (Scheme.kernelInclusion f)).mp
  rw [MonObj.mul_comp, pointDifference_comp_inclusion,
    pointDifference_comp_inclusion, pointDifference_comp_inclusion]
  simp only [mul_assoc, mul_inv_cancel_left]

@[simp]
theorem pointDifference_self {T : C} (x : T ⟶ A) :
    pointDifference f x x rfl = 1 := by
  apply (cancel_mono (Scheme.kernelInclusion f)).mp
  rw [pointDifference_comp_inclusion, MonObj.one_comp, inv_mul_cancel]

/-- Reversing a fiber relation inverts the corresponding kernel element. -/
theorem pointDifference_reverse {T : C} (x y : T ⟶ A) (h : x ≫ f = y ≫ f) :
    pointDifference f y x h.symm = (pointDifference f x y h)⁻¹ := by
  apply (cancel_mono (Scheme.kernelInclusion f)).mp
  rw [GrpObj.inv_comp, pointDifference_comp_inclusion, pointDifference_comp_inclusion,
    mul_inv_rev, inv_inv]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Pair
