import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion
import Mathlib.LinearAlgebra.Basis.Submodule

/-! # Rational Periods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods

noncomputable section

/-! The rational span of the actual native integral period lattice has
a constructed basis and rank twice the intrinsic complex dimension. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

local instance : AlgebraicGeometry.IsIntegral A.toOver.left := A.variety.property

def rationalPeriods : Submodule ℚ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A) :=
  Submodule.span ℚ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A : Set (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A))

local instance : IsZLattice ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full Torsion.IntrinsicTorsion.e06Input A

def realPeriodBasis := (Torsion.IntrinsicTorsion.periodBasis A).ofZLatticeBasis ℝ

theorem rationalPeriods_eq_span : rationalPeriods A =
    Submodule.span ℚ (Set.range (realPeriodBasis A)) := by
  change Submodule.span ℚ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A : Set (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) = _
  rw [← (Torsion.IntrinsicTorsion.periodBasis A).ofZLatticeBasis_span ℝ]
  exact Submodule.span_span_of_tower ℤ ℚ _

/-- The native integral marking is also a basis of the rational period
space, with the same literal vectors in the complex tangent space. -/
def rationalPeriodBasis : Module.Basis
    (Fin (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom)) ℚ (rationalPeriods A) :=
  (Module.Basis.span ((realPeriodBasis A).linearIndependent.restrict_scalars' ℚ)).map
    (LinearEquiv.ofEq _ _ (rationalPeriods_eq_span A).symm)

instance rationalPeriods_finite : Module.Finite ℚ (rationalPeriods A) :=
  Module.Finite.of_basis (rationalPeriodBasis A)

theorem rationalPeriods_finrank : Module.finrank ℚ (rationalPeriods A) =
    2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom := by
  rw [Module.finrank_eq_card_basis (rationalPeriodBasis A), Fintype.card_fin]

theorem rationalPeriodBasis_coe (i : Fin (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom)) :
    (rationalPeriodBasis A i).val = (Torsion.IntrinsicTorsion.periodBasis A i).val := by
  change (Module.Basis.span ((realPeriodBasis A).linearIndependent.restrict_scalars' ℚ) i).val = _
  exact (Module.Basis.coe_span_apply _ i).trans
    (Module.Basis.ofZLatticeBasis_apply ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (Torsion.IntrinsicTorsion.periodBasis A) i)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods
