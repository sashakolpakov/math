/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechCochains.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.Limits

/-! # Group Product Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.GroupProductCoordinates.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
universe u v w

/-- The categorical product of additive commutative groups is isomorphic to the
corresponding dependent function group. -/
noncomputable def productIsoPi {ι : Type u} (X : ι → AddCommGrpCat.{u}) :
    ∏ᶜ X ≅ .of (∀ i, X i) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (AddCommGrpCat.HasLimit.productLimitCone X).isLimit

/-- The forward product isomorphism is componentwise projection. -/
@[simp]
theorem productIsoPi_hom_apply {ι : Type u} (X : ι → AddCommGrpCat.{u})
    (x : (∏ᶜ X :)) (i : ι) : (productIsoPi X).hom x i = Pi.π X i x :=
  ConcreteCategory.congr_hom
    (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _)
      (AddCommGrpCat.HasLimit.productLimitCone X).isLimit ⟨i⟩) x

/-- Every component of the inverse product isomorphism is evaluation. -/
@[simp]
theorem productIsoPi_inv_apply {ι : Type u} (X : ι → AddCommGrpCat.{u})
    (x : ∀ i, X i) (i : ι) : Pi.π X i ((productIsoPi X).inv x) = x i :=
  ConcreteCategory.congr_hom
    (IsLimit.conePointUniqueUpToIso_inv_comp (limit.isLimit _)
      (AddCommGrpCat.HasLimit.productLimitCone X).isLimit ⟨i⟩) x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.GroupProductCoordinates.IntrinsicCech
