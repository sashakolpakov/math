import OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Refinement

/-! # Period Cochain -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PeriodCochain

noncomputable section

/-!
# ChernClass: integral exponential periods in every Cech degree

Continuous complex cochains whose exponential is one have locally constant
integer periods. Their rationalizations are uniquely determined by multiplying
back by the actual exponential period `2πi`.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {I : Type} (X : TopCat.{0}) (U : I → Opens X) (n : ℕ)

/-- The actual integer exponential periods, rationalized on each intersection. -/
def periodCochain (c : Rational.Cech.RationalCech.CechCochain (LogCech.RationalCech.continuousComplexPresheaf X) U n)
    (h : ∀ a x, Complex.exp (c a x) = 1) : Rational.Cech.RationalCech.CechCochain (Cech.Obj.RationalCech.locallyConstantPresheaf X) U n :=
  fun a => {
    toFun x := (Logarithms.Construction.logarithmicDefect (c a x) 0 0
      (by simpa only [Complex.exp_zero, mul_one] using h a x) : ℚ)
    isLocallyConstant := (Logarithms.Construction.isLocallyConstant_logarithmicDefect (c a) 0 0
      (fun x => by simpa only [Complex.exp_zero, ContinuousMap.zero_apply, mul_one] using h a x)).comp
        (fun m : ℤ => (m : ℚ)) }

/-- Multiplying the integer period by `2πi` recovers the supplied cochain. -/
theorem periodMap_periodCochain (c : Rational.Cech.RationalCech.CechCochain (LogCech.RationalCech.continuousComplexPresheaf X) U n)
    (h : ∀ a x, Complex.exp (c a x) = 1) :
    Rational.Cech.RationalCech.cechCoefficientMap U (LogCech.RationalCech.periodMap X) n (periodCochain X U n c h) = c := by
  funext a
  apply ContinuousMap.ext
  intro x
  have hp := Logarithms.Construction.logarithmicDefect_spec (c a x) 0 0
    (by simpa only [Complex.exp_zero, mul_one] using h a x)
  change (((Logarithms.Construction.logarithmicDefect _ _ _ _ : ℤ) : ℚ) : ℂ) * _ = c a x
  push_cast
  simpa only [add_zero, sub_zero] using hp.symm

/-- Every rational cochain whose period image is the supplied complex cochain
is the constructed integral-period cochain. -/
theorem periodCochain_unique (c : Rational.Cech.RationalCech.CechCochain (LogCech.RationalCech.continuousComplexPresheaf X) U n)
    (h : ∀ a x, Complex.exp (c a x) = 1)
    (q : Rational.Cech.RationalCech.CechCochain (Cech.Obj.RationalCech.locallyConstantPresheaf X) U n)
    (hq : Rational.Cech.RationalCech.cechCoefficientMap U (LogCech.RationalCech.periodMap X) n q = c) : q = periodCochain X U n c h :=
  LogCech.RationalCech.periodCechMap_injective X U n (hq.trans (periodMap_periodCochain X U n c h).symm)

/-- An integral-period cochain is closed whenever its complex cochain is closed. -/
theorem periodCochain_closed (c : Rational.Cech.RationalCech.CechCochain (LogCech.RationalCech.continuousComplexPresheaf X) U n)
    (h : ∀ a x, Complex.exp (c a x) = 1)
    (hc : Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U n c = 0) :
    Rational.Cech.RationalCech.cechDelta (Cech.Obj.RationalCech.locallyConstantPresheaf X) U n (periodCochain X U n c h) = 0 := by
  apply LogCech.RationalCech.periodCechMap_injective X U (n + 1)
  rw [Rational.Cech.RationalCech.cechCoefficientMap_delta, periodMap_periodCochain, hc, map_zero]

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PeriodCochain
