import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Cochain Scalar Restriction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CochainScalarRestriction.Construction

noncomputable section

/-! Actual cochain complexes and differential kernels under restriction of scalars. -/

open _root_.CategoryTheory

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (ρ : R →+* S)

abbrev scalarRestrictedComplex (C : CochainComplex (ModuleCat.{u} S) ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  ((ModuleCat.restrictScalars ρ).mapHomologicalComplex (ComplexShape.up ℕ)).obj C

/-- Restriction of scalars leaves the actual zero-cycle elements unchanged. -/
def scalarRestrictedZeroCyclesEquiv (C : CochainComplex (ModuleCat.{u} S) ℕ) :
    (ModuleCat.restrictScalars ρ).obj (ModuleCat.of S (C.d 0 1).hom.ker) ≃ₗ[R]
      ((scalarRestrictedComplex ρ C).d 0 1).hom.ker where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem scalarRestrictedZeroCyclesEquiv_apply_val (C : CochainComplex (ModuleCat.{u} S) ℕ)
    (x : (ModuleCat.restrictScalars ρ).obj (ModuleCat.of S (C.d 0 1).hom.ker)) :
    (scalarRestrictedZeroCyclesEquiv ρ C x).val = x.val := rfl

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CochainScalarRestriction.Construction
