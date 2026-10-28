import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraRecoverySpec

/-! # Subalgebra Base Inclusion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraBaseInclusion

noncomputable section

/-! Inclusion of the original coefficient ring into the final subalgebra gives the direct base-change morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra A R]

def subalgebraBaseInclusion (C : Subalgebra ℤ R) (D : Subalgebra A R) (h : C ≤ D.restrictScalars ℤ) :
    C →+* D where
  toFun x := ⟨x.val, h x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def subalgebraBaseInclusionSpec (C : Subalgebra ℤ R) (D : Subalgebra A R) (h : C ≤ D.restrictScalars ℤ) :
    SubalgebraRecoverySpec.subalgebraBaseScheme D ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom (subalgebraBaseInclusion C D h))

theorem subalgebraBaseInclusion_recovery (C : Subalgebra ℤ R) (D : Subalgebra A R)
    (h : C ≤ D.restrictScalars ℤ) :
    SubalgebraRecoverySpec.subalgebraRecoverySpec (C := A) (R := R) D ≫ subalgebraBaseInclusionSpec C D h =
      SubalgebraRecoverySpec.subalgebraRecoverySpec (C := ℤ) (R := R) C := by
  change Spec.map (CommRingCat.ofHom D.val.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (subalgebraBaseInclusion C D h)) = Spec.map (CommRingCat.ofHom C.val.toRingHom)
  rw [← Spec.map_comp]
  congr 1

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraBaseInclusion
