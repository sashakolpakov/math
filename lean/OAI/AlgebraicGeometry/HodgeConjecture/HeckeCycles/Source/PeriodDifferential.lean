import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq

/-! # Period Differential -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PeriodDifferential.CM

noncomputable section

/-! Differentiate the original negative-line action. Pairing with its
annihilator removes the derivative of the scalar line frame, producing
the exact cotangent factor required by the source theta projection. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PrescribedAction

def tangent : GeometricSource.CM.BallChart →L[ℂ] GeometricSource.CM.Vec ℂ :=
  (show GeometricSource.CM.BallChart →ₗ[ℂ] GeometricSource.CM.Vec ℂ from
    { toFun := fun ξ => ![ξ 0, ξ 1, 0]
      map_add' := by intro x y; ext i; fin_cases i <;> simp
      map_smul' := by intro c x; ext i; fin_cases i <;> simp }).toContinuousLinearMap

theorem tangent_apply (ξ : GeometricSource.CM.BallChart) : tangent ξ = ![ξ 0, ξ 1, 0] := rfl

theorem lineVector_hasFDerivAt (z : GeometricSource.CM.BallChart) :
    HasFDerivAt GeometricSource.CM.BallDatum.lineVector tangent z := by
  have he : GeometricSource.CM.BallDatum.lineVector = fun x => tangent x + ![0, 0, 1] := by
    funext x i
    fin_cases i <;> simp [GeometricSource.CM.BallDatum.lineVector, tangent_apply]
  rw [he]
  exact tangent.hasFDerivAt.add_const _

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E}

def lineScale (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) : ℂ :=
  UnitaryEq.CM.Frames.localAction E g 1 (GeometricSource.CM.BallDatum.lineVector z) 2

theorem line_scale_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    UnitaryEq.CM.Frames.localAction E g 1 (GeometricSource.CM.BallDatum.lineVector z) =
      lineScale E g z • GeometricSource.CM.BallDatum.lineVector (UnitaryEq.CM.Frames.period E g z) := by
  obtain ⟨c, _, he⟩ := UnitaryEq.CM.Frames.line_action E g z hz
  have hc : lineScale E g z = c := by
    have h := congrFun he 2
    change lineScale E g z = c * 1 at h
    simpa only [mul_one] using h
  rw [hc]
  exact he

theorem lineScale_ne_zero (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) : lineScale E g z ≠ 0 := by
  obtain ⟨c, hc, he⟩ := UnitaryEq.CM.Frames.line_action E g z hz
  have h : lineScale E g z = c := by
    have h := congrFun he 2
    change lineScale E g z = c * 1 at h
    simpa only [mul_one] using h
  exact h ▸ hc

theorem lineScale_differentiableAt (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) :
    DifferentiableAt ℂ (lineScale E g) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 2).differentiableAt.comp z
    ((LinearMap.toContinuousLinearMap (UnitaryEq.CM.Frames.localAction E g 1)).differentiableAt.comp z
      (lineVector_hasFDerivAt z).differentiableAt)

theorem period_differentiableAt (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) : DifferentiableAt ℂ (UnitaryEq.CM.Frames.period E g) z :=
  (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm_differentiableOn B.b E.val.toRingHom g z hz).differentiableAt
    (B.domain_isOpen.mem_nhds hz)

theorem line_differential (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (ξ : GeometricSource.CM.BallChart) :
    UnitaryEq.CM.Frames.localAction E g 1 (tangent ξ) =
      lineScale E g z • tangent (fderiv ℂ (UnitaryEq.CM.Frames.period E g) z ξ) +
        fderiv ℂ (lineScale E g) z ξ • GeometricSource.CM.BallDatum.lineVector (UnitaryEq.CM.Frames.period E g z) := by
  have hl := (LinearMap.toContinuousLinearMap (UnitaryEq.CM.Frames.localAction E g 1)).hasFDerivAt.comp z
    (lineVector_hasFDerivAt z)
  have hr := (lineScale_differentiableAt E g z).hasFDerivAt.smul
    ((lineVector_hasFDerivAt (UnitaryEq.CM.Frames.period E g z)).comp z
      (period_differentiableAt E g z hz).hasFDerivAt)
  have he : (fun x => UnitaryEq.CM.Frames.localAction E g 1 (GeometricSource.CM.BallDatum.lineVector x)) =ᶠ[nhds z]
      (fun x => lineScale E g x • GeometricSource.CM.BallDatum.lineVector (UnitaryEq.CM.Frames.period E g x)) :=
    Filter.eventually_of_mem (B.domain_isOpen.mem_nhds hz) (fun x hx => line_scale_action E g x hx)
  have h := hl.unique (hr.congr_of_eventuallyEq he)
  exact congrArg (fun f : GeometricSource.CM.BallChart →L[ℂ] GeometricSource.CM.Vec ℂ => f ξ) h

theorem pairing_add_left (τ : Gal(E/ℚ)) (x y w : GeometricSource.CM.Vec ℂ) :
    GeometricSource.CM.localPairing E B.b τ (x + y) w =
      GeometricSource.CM.localPairing E B.b τ x w + GeometricSource.CM.localPairing E B.b τ y w := by
  simp only [GeometricSource.CM.localPairing, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem cotangent_covariance (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (ξ : GeometricSource.CM.BallChart) (w : GeometricSource.CM.Vec ℂ)
    (hw : GeometricSource.CM.localPairing E B.b 1 (GeometricSource.CM.BallDatum.lineVector z) w = 0) :
    lineScale E g z * GeometricSource.CM.localPairing E B.b 1
      (tangent (fderiv ℂ (UnitaryEq.CM.Frames.period E g) z ξ)) (UnitaryEq.CM.Frames.localAction E g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) w) =
    GeometricSource.CM.localPairing E B.b 1 (tangent ξ) w := by
  have hpair := UnitaryEq.CM.Frames.pairing_preserved E g 1 (GeometricSource.CM.BallDatum.lineVector z) w
  rw [mul_one, line_scale_action E g z hz, UnitaryEq.CM.PrescribedAction.pairing_smul_left, hw] at hpair
  have hann := (mul_eq_zero.mp hpair).resolve_left (lineScale_ne_zero E g z hz)
  have h := UnitaryEq.CM.Frames.pairing_preserved E g 1 (tangent ξ) w
  rw [mul_one, line_differential E g z hz ξ, pairing_add_left,
    UnitaryEq.CM.PrescribedAction.pairing_smul_left, UnitaryEq.CM.PrescribedAction.pairing_smul_left, hann, mul_zero, add_zero] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PeriodDifferential.CM
