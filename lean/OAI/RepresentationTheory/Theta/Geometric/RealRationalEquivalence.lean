import OAI.RepresentationTheory.Theta.Geometric.RealPeriodCoe

/-! # Real Rational Equivalence -/

namespace OAI.RepresentationTheory.Theta.Geometric.RealRationalEquivalence

noncomputable section

/-! An actual real linear equivalence identifying the full native
lattices identifies their original rational spans as well. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

namespace RealPeriodMaps

local instance realRationalEquivalence_integral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property

variable {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (T : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃L[ℝ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)
    (h : ∀ v, T v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B ↔ v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)

include h in
theorem symm_preserves (v : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B) (hv : v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B) :
    T.symm v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A :=
  (h (T.symm v)).mp (by simpa only [T.apply_symm_apply] using hv)

def rationalEquiv : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B := by
  let f := RealPeriodCoe.RealPeriodMaps.rationalMap T.toContinuousLinearMap (fun v hv => (h v).mpr hv)
  let g := RealPeriodCoe.RealPeriodMaps.rationalMap T.symm.toContinuousLinearMap (symm_preserves T h)
  apply LinearEquiv.ofLinearMap f g
  · apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact T.apply_symm_apply v.val
  · apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact T.symm_apply_apply v.val

theorem rationalEquiv_apply (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    rationalEquiv T h v = RealPeriodCoe.RealPeriodMaps.rationalMap T.toContinuousLinearMap (fun v hv => (h v).mpr hv) v := rfl

end RealPeriodMaps

end

end OAI.RepresentationTheory.Theta.Geometric.RealRationalEquivalence
