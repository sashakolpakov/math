import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods
import Mathlib.RingTheory.Finiteness.Basic

/-! # Rational Lattice -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods

noncomputable section

/-! Embed the actual integral period lattice in its rational span. The
embedded lattice is finitely generated and spans that rational space. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

local instance : AlgebraicGeometry.IsIntegral A.toOver.left := A.variety.property

def integralPeriods : Submodule ℤ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :=
  (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A).comap ((RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A).subtype.restrictScalars ℤ)

def integralPeriodsEquiv : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A ≃ₗ[ℤ] integralPeriods A where
  toFun v := ⟨⟨v.val, Submodule.subset_span v.property⟩, v.property⟩
  invFun v := ⟨v.val.val, v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem integralPeriods_fg : (integralPeriods A).FG := by
  let : Module.Finite ℤ (integralPeriods A) :=
    Module.Finite.of_basis ((Torsion.IntrinsicTorsion.periodBasis A).map (integralPeriodsEquiv A))
  exact Module.Finite.iff_fg.mp inferInstance

theorem integralPeriods_image :
    (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A).subtype '' (integralPeriods A : Set (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) =
      (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A : Set (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hv
    exact ⟨⟨v, Submodule.subset_span hv⟩, hv, rfl⟩

theorem integralPeriods_span :
    Submodule.span ℚ (integralPeriods A : Set (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) = ⊤ := by
  apply Submodule.map_injective_of_injective (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A).subtype_injective
  rw [Submodule.map_span, integralPeriods_image, Submodule.map_top, Submodule.range_subtype]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods
