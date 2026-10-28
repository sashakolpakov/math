import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IsoCoefficient
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DivisorChow

/-! # Iso Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IsoDivisor.Cycles

noncomputable section

/-! # LineBundleCycles: isomorphic line bundles have rational-section divisors differing by an actual principal divisor -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] {L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X} (e : L.sheaf ≅ M.sheaf)

theorem lineBundleIso_order [IsLocallyNoetherian X] (x : X) :
    M.rationalSectionOrder x + X.ord (IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient e).val x = L.rationalSectionOrder x := by
  have h := congrArg (fun a : X.functionFieldˣ => X.ord a.val x) (IsoCoefficient.Cycles.lineBundleIso_coordinate_identity e x)
  change X.ord ((M.rationalSectionCoordinate x).val * (IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient e).val) x =
    X.ord ((FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm (IsoCoefficient.Cycles.lineBundleIsoLocalOpen L M x) (IsoCoefficient.Cycles.lineBundleIsoLocalUnit e x)).val *
      (L.rationalSectionCoordinate x).val) x at h
  rw [Scheme.ord_mul (M.rationalSectionCoordinate_ne_zero x) (IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient e).ne_zero,
    Scheme.ord_mul (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm _ _).ne_zero (L.rationalSectionCoordinate_ne_zero x),
    IsoCoefficient.Cycles.lineBundleIsoLocalUnit_order, zero_add] at h
  exact h

variable [AlgebraicGeometry.IsNoetherian X]

theorem lineBundleIso_divisor :
    L.rationalSectionPointDivisor = M.rationalSectionPointDivisor + Ord.BundleCycles.principalDivisor X (IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient e).val := by
  ext x
  exact (lineBundleIso_order e x).symm

theorem lineBundleIso_pointCycle :
    L.rationalSectionPointCycle = M.rationalSectionPointCycle +
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient e).val := by
  ext x
  exact (congrArg (fun n : ℤ => (n : ℚ)) (lineBundleIso_order e x)).symm.trans (Int.cast_add _ _)

include e in
theorem lineBundleIso_chowClass (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) :
    L.rationalSectionChowClass f d = M.rationalSectionChowClass f d := by
  change Point.CycleChow.BundleCycles.pointCycleToChowQ f d L.rationalSectionPointCycle = _
  rw [lineBundleIso_pointCycle e, map_add, Integral.PrincipalChow.BundleCycles.integralPrincipalPointClass_zero X f d hd, add_zero]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IsoDivisor.Cycles
