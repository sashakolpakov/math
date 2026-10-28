import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods

/-! # Period Bilinear Ext -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.PeriodBilinearExt

noncomputable section

/-! The actual rational period vectors determine a real bilinear form
on the native tangent space. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods

theorem realPeriodBilinear_ext (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (B C : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℝ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →ₗ[ℝ] W)
    (h : ∀ v w : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A, B v.val w.val = C v.val w.val) : B = C := by
  let : AlgebraicGeometry.IsIntegral A.toOver.left := A.variety.property
  let : IsZLattice ℝ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice_full Intrinsic.Torsion.IntrinsicTorsion.e06Input A
  have he (i : Fin (2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom)) :
      Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A i = (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i).val :=
    (Module.Basis.ofZLatticeBasis_apply ℝ _ (Intrinsic.Torsion.IntrinsicTorsion.periodBasis A) i).trans
      (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis_coe A i).symm
  apply (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).ext
  intro i
  apply (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.realPeriodBasis A).ext
  intro j
  exact (congrArg₂ (fun x y => B x y) (he i) (he j)).trans
    ((h (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A i) (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriodBasis A j)).trans
      (congrArg₂ (fun x y => C x y) (he i) (he j)).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.PeriodBilinearExt
