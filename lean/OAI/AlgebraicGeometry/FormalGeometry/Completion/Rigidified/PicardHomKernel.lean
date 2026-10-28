import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ZeroSubgroupClosed
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.SheafMonoid

/-! # Picard Hom Kernel -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified

noncomputable section

/-! A multiplicative actual Picard-family map has a subgroup zero
condition. No represented Picard target is required. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.SheafMonoid
open scoped _root_.CategoryTheory.MonObj

universe u
variable {K : Type u} [Field K] {A B : Over (Spec (.of K))} [GrpObj A] [GrpObj B]
  (D : ProductLine.Construction.RigidifiedProductLine A B)

theorem ProductLine.Construction.RigidifiedProductLine.zeroIsSubgroup_of_relative_mul
    (h1 : ∀ T : Over (Spec (.of K)), D.relativeValue (1 : T ⟶ B) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T)
    (hmul : ∀ {T : Over (Spec (.of K))} (a b : T ⟶ B),
      D.relativeValue (a * b) = D.relativeValue a * D.relativeValue b) : D.ZeroIsSubgroup where
  one := h1
  mul a b ha hb := by
    rw [hmul, ha, hb, AbelianModuli.HilbertConstruction.Picard.SheafMonoid.trivialPicardClass_eq_one, one_mul]
  inv a ha := by
    have h : D.relativeValue a * D.relativeValue a⁻¹ = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A _ := by
      rw [← hmul, mul_inv_cancel, h1]
    rw [ha, AbelianModuli.HilbertConstruction.Picard.SheafMonoid.trivialPicardClass_eq_one, one_mul] at h
    simpa only [AbelianModuli.HilbertConstruction.Picard.SheafMonoid.trivialPicardClass_eq_one] using h

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified
