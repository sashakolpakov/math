import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SmoothLocal
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SurjectiveReductionEq
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Power

/-! # Power Local -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.PowerLocal.PowerLocalLifting

/-!
# TorsionQuotient: local infinitesimal lifts of multiplication by an invertible integer

Smoothness first lifts a point over the base. Its power error reduces to the
identity, so the unique infinitesimal root corrects the lift.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A] [Smooth A.hom]
variable {C B : CommRingCat.{u}} [IsLocalRing C] [IsLocalRing B]
variable (s : Spec C ⟶ S) (p : C ⟶ B) (hp : Function.Surjective p)
variable (hker : RingHom.ker p.hom ^ 2 = ⊥) (n : ℕ) (hn : IsUnit (n : C))

include hp hker hn in
theorem exists_power_lift
    (a : Over.mk (Spec.map p ≫ s) ⟶ A) (b : Over.mk s ⟶ A)
    (hab : a ^ n = SurjectiveReductionEq.SurjectiveReduction.reduction s p A b) :
    ∃ l : Over.mk s ⟶ A,
      SurjectiveReductionEq.SurjectiveReduction.reduction s p A l = a ∧ l ^ n = b := by
  obtain ⟨l, hl, hls⟩ := SmoothLocal.SmoothLocalLifting.exists_scheme_lift A.hom p hp hker a.left s (Over.w a)
  let l' : Over.mk s ⟶ A := Over.homMk l hls
  have hl' : SurjectiveReductionEq.SurjectiveReduction.reduction s p A l' = a := by
    apply Over.OverMorphism.ext
    exact hl
  have he : SurjectiveReductionEq.SurjectiveReduction.reduction s p A (b / l' ^ n) = 1 := by
    rw [map_div, map_pow, hl', ← hab, div_self']
  obtain ⟨c, hc, hcn⟩ := SurjectiveReductionEq.SurjectiveReduction.exists_root_in_kernel s p hp hker A n hn
    (b / l' ^ n) he
  refine ⟨l' * c, ?_, ?_⟩
  · rw [map_mul, hl', hc, mul_one]
  · rw [mul_pow, hcn]
    simp only [div_eq_mul_inv, ← mul_assoc, mul_comm (l' ^ n) b, mul_inv_cancel_right]

include hp hker in
theorem exists_scheme_power_lift
    (hunit : ∀ x : S, IsUnit (n : S.presheaf.stalk x))
    (a : Spec B ⟶ A.left) (b : Spec C ⟶ A.left)
    (hab : a ≫ ((𝟙 A : A ⟶ A) ^ n).left = Spec.map p ≫ b) :
    ∃ l : Spec C ⟶ A.left,
      Spec.map p ≫ l = a ∧ l ≫ ((𝟙 A : A ⟶ A) ^ n).left = b := by
  let s := b ≫ A.hom
  have ha : a ≫ A.hom = Spec.map p ≫ s := by
    have h := congrArg (fun z => z ≫ A.hom) hab
    simpa only [Category.assoc, Over.w] using h
  let α : Over.mk (Spec.map p ≫ s) ⟶ A := Over.homMk a ha
  let β : Over.mk s ⟶ A := Over.homMk b rfl
  have hab' : α ^ n = SurjectiveReductionEq.SurjectiveReduction.reduction s p A β := by
    apply Over.OverMorphism.ext
    change (α ≫ (𝟙 A : A ⟶ A) ^ n).left =
      (SurjectiveReductionEq.SurjectiveReduction.reduction s p A β).left at hab
    simpa only [MonObj.comp_pow, Category.comp_id] using hab
  obtain ⟨l, hl, hln⟩ := exists_power_lift A s p hp hker n
    (Power.PowerGeometry.unit_on_local_test n hunit s) α β hab'
  refine ⟨l.left, congrArg (fun z => z.left) hl, ?_⟩
  change (l ≫ (𝟙 A : A ⟶ A) ^ n).left = b
  rw [MonObj.comp_pow, Category.comp_id, hln]
  rfl

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.PowerLocal.PowerLocalLifting
