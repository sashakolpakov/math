import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticePeriodEvaluation

/-! # Marking Rational Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.MarkingRationalBasis

noncomputable section

/-! Extend an arbitrary original integral period marking to the
rational period space while keeping its basis vectors unchanged. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods

variable {ι : Type} [Fintype ι] (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
  (b : Module.Basis ι ℤ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A))

local instance : IsZLattice ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full Intrinsic.Torsion.IntrinsicTorsion.e06Input A

omit [Fintype ι] in
theorem rationalPeriods_eq_marking_span : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A =
    Submodule.span ℚ (Set.range (b.ofZLatticeBasis ℝ)) := by
  change Submodule.span ℚ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A : Set (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) = _
  conv_lhs => arg 2; rw [← b.ofZLatticeBasis_span ℝ]
  exact Submodule.span_span_of_tower ℤ ℚ _

def integralMarkingRationalBasis : Module.Basis ι ℚ (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :=
  (Module.Basis.span ((b.ofZLatticeBasis ℝ).linearIndependent.restrict_scalars' ℚ)).map
    (LinearEquiv.ofEq _ _ (rationalPeriods_eq_marking_span A b).symm)

omit [Fintype ι] in
theorem integralMarkingRationalBasis_coe (i : ι) :
    (integralMarkingRationalBasis A b i).val = (b i).val := by
  change (Module.Basis.span ((b.ofZLatticeBasis ℝ).linearIndependent.restrict_scalars' ℚ) i).val = _
  exact (Module.Basis.coe_span_apply _ i).trans
    (Module.Basis.ofZLatticeBasis_apply ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) b i)

omit [Fintype ι] in
theorem integralMarkingRationalBasis_eq (i : ι) :
    integralMarkingRationalBasis A b i =
      LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (b i) := by
  apply Subtype.ext
  exact integralMarkingRationalBasis_coe A b i

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.MarkingRationalBasis
