import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Lift Detection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.LiftDetection.CM

noncomputable section

/-! A real metaplectic lift is determined by its projection and its
action on one nonzero Schwartz vector. The only possible ambiguity is
the genuine central sign, which a nonzero vector detects. -/

open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem real_eq_of_nonzero_vector (r s : MpR) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz ι)
    (hf : f ≠ 0) (hp : W.real.project r = W.real.project s)
    (ha : W.real.action r f = W.real.action s f) : r = s := by
  have hk : W.real.project (r * s⁻¹) = 1 := by
    rw [map_mul, map_inv, hp, mul_inv_cancel]
  rcases (W.real.kernel _).mp hk with h | h
  · exact mul_inv_eq_one.mp h
  · have hr : r = W.real.negOne * s := mul_inv_eq_iff_eq_mul.mp h
    rw [hr, map_mul, LinearEquiv.mul_apply, W.real.genuine] at ha
    have hz : W.real.action s f = 0 := by
      apply Subtype.ext
      funext x
      have hx := congrArg (fun t : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz ι => t.val x) ha
      exact CharZero.neg_eq_self_iff.mp hx
    exact (hf ((W.real.action s).map_eq_zero_iff.mp hz)).elim

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.LiftDetection.CM
