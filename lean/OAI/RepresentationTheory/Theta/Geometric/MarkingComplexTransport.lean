import OAI.RepresentationTheory.Theta.Geometric.Period.VarietyMarkedAbelianPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection

/-! # Marking Complex Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric.MarkingComplexTransport

noncomputable section

section

/-! Rational and complex coordinates of any actual full integral marking.
The coordinate maps retain the literal native period vectors. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods

variable {ι : Type} {A : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
local instance markingRationalCoordinates_integral : AlgebraicGeometry.IsIntegral A.toOver.left := A.variety.property
local instance markingRationalCoordinates_full : IsZLattice ℝ (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :=
  OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input A

theorem marking_rational_span (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A) :
    OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A = Submodule.span ℚ (Set.range (b.ofZLatticeBasis ℝ (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A))) := by
  change Submodule.span ℚ (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A : Set (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) = _
  conv_lhs => rw [← b.ofZLatticeBasis_span ℝ]
  exact Submodule.span_span_of_tower ℤ ℚ _

def markingRationalBasis (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A) : Module.Basis ι ℚ (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :=
  (Module.Basis.span ((b.ofZLatticeBasis ℝ (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)).linearIndependent.restrict_scalars' ℚ)).map
    (LinearEquiv.ofEq _ _ (marking_rational_span b).symm)

theorem markingRationalBasis_coe (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A) (i : ι) :
    (markingRationalBasis b i).val = (b i).val := by
  change (Module.Basis.span ((b.ofZLatticeBasis ℝ (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)).linearIndependent.restrict_scalars' ℚ) i).val = _
  exact (Module.Basis.coe_span_apply _ i).trans (b.ofZLatticeBasis_apply ℝ (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) i)

def markingComplexBasis (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A) : Module.Basis ι ℂ (OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :=
  (markingRationalBasis b).baseChange ℂ

theorem markingComplexBasis_apply (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A) (i : ι) :
    markingComplexBasis b i = 1 ⊗ₜ[ℚ] markingRationalBasis b i :=
  Module.Basis.baseChange_apply ℂ (markingRationalBasis b) i

theorem markingComplexBasis_projection (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A) (i : ι) :
    OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A (markingComplexBasis b i) = (b i).val := by
  rw [markingComplexBasis_apply, OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection_tmul, one_smul, markingRationalBasis_coe]

variable [Fintype ι]

theorem complexPeriodProjection_marking (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A) (u : OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u = ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b ((markingComplexBasis b).equivFun u) := by
  have h := congrArg (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A) ((markingComplexBasis b).sum_repr u)
  simpa only [map_sum, map_smul, markingComplexBasis_projection,
    ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap_apply, Module.Basis.equivFun_apply] using h.symm

end

/-! A rational map carrying actual marked lattice vectors carries their
complexified bases and retains every complex coordinate. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods

variable {ι : Type} {A B : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking ι A) (c : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking ι B)
    (f : OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B)
    (hf : ∀ i, f (markingRationalBasis b i) = markingRationalBasis c i)

include hf in
theorem markingComplexBasis_transport (i : ι) :
    f.baseChange ℂ (markingComplexBasis b i) = markingComplexBasis c i := by
  rw [markingComplexBasis_apply, LinearMap.baseChange_tmul, hf, markingComplexBasis_apply]

variable [Fintype ι]

include hf in
theorem markingComplexCoordinates_transport (u : OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    (markingComplexBasis c).equivFun (f.baseChange ℂ u) = (markingComplexBasis b).equivFun u := by
  classical
  have he : (markingComplexBasis c).equivFun.toLinearMap.comp (f.baseChange ℂ) =
      (markingComplexBasis b).equivFun.toLinearMap := by
    apply (markingComplexBasis b).ext
    intro i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      markingComplexBasis_transport b c f hf]
    funext j
    simp only [Module.Basis.equivFun_self]
  exact LinearMap.congr_fun he u

include hf in
theorem complexPeriodProjection_transport_marking (u : OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection B (f.baseChange ℂ u) =
      ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap c ((markingComplexBasis b).equivFun u) := by
  rw [complexPeriodProjection_marking c, markingComplexCoordinates_transport b c f hf]

end

end OAI.RepresentationTheory.Theta.Geometric.MarkingComplexTransport
