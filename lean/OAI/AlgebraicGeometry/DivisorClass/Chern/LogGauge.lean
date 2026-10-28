import OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech

/-! # Log Gauge -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.LogGauge

noncomputable section

section

/-!
# ChernClass: invariance under logarithmic changes of frame

Adding the Cech coboundary of logarithms of frame changes preserves the
integral defect. Any other logarithms with these exponentials give the same
rational singular class as well.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {I : Type} (X : TopCat.{0}) (U : I → Opens X)

/-- The degree-one Cech differential is the usual three-term logarithmic defect. -/
theorem logCechDelta_apply (l : LogCech.RationalCech.LogCechCochain X U) (a : Fin 3 → I)
    (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :
    Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 1 l a x =
      LogCech.RationalCech.edgeLog X U l 2 a x + LogCech.RationalCech.edgeLog X U l 0 a x - LogCech.RationalCech.edgeLog X U l 1 a x := by
  rw [Rational.Cech.RationalCech.cechDelta_apply, Fin.sum_univ_three]
  change (1 : ℤ) • LogCech.RationalCech.edgeLog X U l 0 a x + (-1 : ℤ) • LogCech.RationalCech.edgeLog X U l 1 a x +
    (1 : ℤ) • LogCech.RationalCech.edgeLog X U l 2 a x = _
  simp only [one_zsmul, neg_one_zsmul]
  ring

/-- The multiplicative transition identity is equivalent to exponentiating
the additive Cech differential to one. -/
theorem exponentialCocycle_iff_delta_exp (l : LogCech.RationalCech.LogCechCochain X U) :
    LogCech.RationalCech.ExponentialCocycle X U l ↔ ∀ (a : Fin 3 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 1 l a x) = 1 := by
  constructor
  · intro h a x
    rw [logCechDelta_apply, Complex.exp_sub, Complex.exp_add]
    exact (div_eq_one_iff_eq (Complex.exp_ne_zero _)).mpr (h a x)
  · intro h a x
    have hx := h a x
    rw [logCechDelta_apply, Complex.exp_sub, Complex.exp_add] at hx
    exact (div_eq_one_iff_eq (Complex.exp_ne_zero _)).mp hx

/-- Equal additive differentials produce equal rationalized integral defects. -/
theorem logDefectCech_eq_of_delta_eq (l l' : LogCech.RationalCech.LogCechCochain X U)
    (h : LogCech.RationalCech.ExponentialCocycle X U l) (h' : LogCech.RationalCech.ExponentialCocycle X U l')
    (hd : Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 1 l =
      Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 1 l') :
    LogCech.RationalCech.logDefectCech X U l h = LogCech.RationalCech.logDefectCech X U l' h' := by
  apply LogCech.RationalCech.periodCechMap_injective X U 2
  rw [LogCech.RationalCech.periodMap_logDefectCech, LogCech.RationalCech.periodMap_logDefectCech, hd]

/-- Shift logarithms by the coboundary of continuous logarithms of a frame change. -/
abbrev gaugeLogCech (l : LogCech.RationalCech.LogCechCochain X U)
    (b : Rational.Cech.RationalCech.CechCochain (LogCech.RationalCech.continuousComplexPresheaf X) U 0) : LogCech.RationalCech.LogCechCochain X U :=
  l + Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 0 b

theorem gaugeLogCech_delta (l : LogCech.RationalCech.LogCechCochain X U)
    (b : Rational.Cech.RationalCech.CechCochain (LogCech.RationalCech.continuousComplexPresheaf X) U 0) :
    Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 1 (gaugeLogCech X U l b) =
      Rational.Cech.RationalCech.cechDelta (LogCech.RationalCech.continuousComplexPresheaf X) U 1 l := by
  rw [gaugeLogCech, map_add, Rational.Cech.RationalCech.cechDelta_squared, add_zero]

/-- A logarithmic frame change preserves the exponential cocycle condition. -/
theorem gaugeLogCech_cocycle (l : LogCech.RationalCech.LogCechCochain X U)
    (h : LogCech.RationalCech.ExponentialCocycle X U l)
    (b : Rational.Cech.RationalCech.CechCochain (LogCech.RationalCech.continuousComplexPresheaf X) U 0) :
    LogCech.RationalCech.ExponentialCocycle X U (gaugeLogCech X U l b) := by
  rw [exponentialCocycle_iff_delta_exp, gaugeLogCech_delta]
  exact (exponentialCocycle_iff_delta_exp X U l).mp h

/-- The singular class is unchanged by a logarithmic frame change. -/
theorem logarithmicSingularClass_gauge (hU : ∀ x : X, ∃ i, x ∈ U i)
    (l : LogCech.RationalCech.LogCechCochain X U) (h : LogCech.RationalCech.ExponentialCocycle X U l)
    (b : Rational.Cech.RationalCech.CechCochain (LogCech.RationalCech.continuousComplexPresheaf X) U 0) :
    LogCech.RationalCech.logarithmicSingularClass X U hU (gaugeLogCech X U l b)
      (gaugeLogCech_cocycle X U l h b) = LogCech.RationalCech.logarithmicSingularClass X U hU l h := by
  have hc : LogCech.RationalCech.logDefectCocycle X U (gaugeLogCech X U l b)
      (gaugeLogCech_cocycle X U l h b) = LogCech.RationalCech.logDefectCocycle X U l h := by
    apply Subtype.ext
    exact logDefectCech_eq_of_delta_eq X U _ _ _ _ (gaugeLogCech_delta X U l b)
  unfold LogCech.RationalCech.logarithmicSingularClass
  rw [hc]

/-- Any logarithms of gauge-equivalent transitions compute the same singular class. -/
theorem logarithmicSingularClass_gauge_of_exp_eq (hU : ∀ x : X, ∃ i, x ∈ U i)
    (l l' : LogCech.RationalCech.LogCechCochain X U) (h : LogCech.RationalCech.ExponentialCocycle X U l)
    (h' : LogCech.RationalCech.ExponentialCocycle X U l')
    (b : Rational.Cech.RationalCech.CechCochain (LogCech.RationalCech.continuousComplexPresheaf X) U 0)
    (he : ∀ (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l' a x) = Complex.exp (gaugeLogCech X U l b a x)) :
    LogCech.RationalCech.logarithmicSingularClass X U hU l' h' = LogCech.RationalCech.logarithmicSingularClass X U hU l h :=
  (LogCech.RationalCech.logarithmicSingularClass_log_independent X U hU l' (gaugeLogCech X U l b)
    h' (gaugeLogCech_cocycle X U l h b) he).trans
    (logarithmicSingularClass_gauge X U hU l h b)

end RationalCech

end

/-!
# ChernClass: zero logarithmic data give the zero singular class
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {I : Type} (X : TopCat.{0}) (U : I → Opens X)

theorem exponentialCocycle_zero : LogCech.RationalCech.ExponentialCocycle X U 0 := by
  intro a x
  change Complex.exp 0 * Complex.exp 0 = Complex.exp 0
  simp only [Complex.exp_zero, mul_one]

theorem logDefectCech_zero : LogCech.RationalCech.logDefectCech X U 0 (exponentialCocycle_zero X U) = 0 := by
  apply LogCech.RationalCech.periodCechMap_injective X U 2
  rw [LogCech.RationalCech.periodMap_logDefectCech, map_zero, map_zero]

theorem logDefectCocycle_zero : LogCech.RationalCech.logDefectCocycle X U 0 (exponentialCocycle_zero X U) = 0 := by
  apply Subtype.ext
  exact logDefectCech_zero X U

theorem logarithmicSingularClass_zero (hU : ∀ x : X, ∃ i, x ∈ U i) :
    LogCech.RationalCech.logarithmicSingularClass X U hU 0 (exponentialCocycle_zero X U) = 0 := by
  unfold LogCech.RationalCech.logarithmicSingularClass Cech.Obj.RationalCech.singularClassOfCechCocycle
  rw [logDefectCocycle_zero, map_zero, map_zero]

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.LogGauge
