import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalCoordinate
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DivisorChow

/-! # Global Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalDivisor.Cycles

noncomputable section

section

/-! # LineBundleCycles: a globally trivialized line bundle has an actual principal reference-section divisor -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X}
    (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X)

theorem lineBundleGlobal_order [IsLocallyNoetherian X] (x : X) :
    L.rationalSectionOrder x = X.ord (GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e).val x := by
  have h := congrArg (fun a : X.functionFieldˣ => X.ord a.val x)
    (GlobalCoordinate.Cycles.lineBundleGlobal_coordinate_identity e x)
  change X.ord ((FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm (L.trivializingOpen x) (GlobalCoordinate.Cycles.lineBundleGlobalLocalUnit e x)).val *
    (L.rationalSectionCoordinate x).val) x = _ at h
  rw [Scheme.ord_mul (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm _ _).ne_zero (L.rationalSectionCoordinate_ne_zero x),
    FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm_order _ _ x (L.mem_trivializingOpen x), zero_add] at h
  exact h

variable [AlgebraicGeometry.IsNoetherian X]

theorem lineBundleGlobal_divisor :
    L.rationalSectionPointDivisor = Ord.BundleCycles.principalDivisor X (GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e).val := by
  ext x
  exact lineBundleGlobal_order e x

theorem lineBundleGlobal_pointCycle :
    L.rationalSectionPointCycle = RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e).val := by
  ext x
  exact congrArg (fun n : ℤ => (n : ℚ)) (lineBundleGlobal_order e x)

include e in
theorem lineBundleGlobal_chowClass (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) : L.rationalSectionChowClass f d = 0 := by
  change Point.CycleChow.BundleCycles.pointCycleToChowQ f d L.rationalSectionPointCycle = 0
  rw [lineBundleGlobal_pointCycle e, Integral.PrincipalChow.BundleCycles.integralPrincipalPointClass_zero X f d hd]

end

/-! # LineBundleCycles: a rational section in an actual global frame has its ordinary principal divisor -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X} (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X)

theorem lineBundleGlobal_section_divisor (a : X.functionFieldˣ) :
    L.rationalSectionPointDivisorWithCoefficient a =
      Ord.BundleCycles.principalDivisor X (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e).val := by
  change Ord.BundleCycles.principalDivisor X a.val + L.rationalSectionPointDivisor = _
  rw [lineBundleGlobal_divisor e]
  exact (Ord.BundleCycles.principalDivisor_mul X _ _ a.ne_zero (GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e).ne_zero).symm

theorem lineBundleGlobal_section_order (a : X.functionFieldˣ) (x : X) :
    L.rationalSectionPointDivisorWithCoefficient a x =
      X.ord (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e).val x :=
  congrArg (fun D : X →₀ ℤ => D x) (lineBundleGlobal_section_divisor e a)

theorem lineBundleGlobal_section_pointCycle (a : X.functionFieldˣ) :
    L.rationalSectionPointCycleWithCoefficient a =
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e).val := by
  change (L.rationalSectionPointDivisorWithCoefficient a).mapRange _ _ = _
  rw [lineBundleGlobal_section_divisor e]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalDivisor.Cycles
