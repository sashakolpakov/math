import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Coercive Hilbert Source -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CoerciveHilbertSource

noncomputable section

/-! A strictly bounded Hilbert energy inclusion gives an actual unshifted variational solver by the convergent resolvent inverse. -/

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def hilbertSourceResolvent (S : E →L[ℂ] H) : H →L[ℂ] H := S.comp S.adjoint

def hilbertSourceUnshifted (S : E →L[ℂ] H) : H →L[ℂ] E :=
  S.adjoint.comp (Ring.inverse (1 - hilbertSourceResolvent S))

theorem hilbertSourceResolvent_norm (S : E →L[ℂ] H) (hS : ‖S‖ ≤ Real.sqrt (1 / 2)) :
    ‖hilbertSourceResolvent S‖ ≤ 1 / 2 := by
  have ha : ‖S.adjoint‖ = ‖S‖ := LinearIsometryEquiv.norm_map _ _
  have hn := S.opNorm_comp_le S.adjoint
  rw [ha, ← pow_two] at hn
  have hs := (sq_le_sq₀ (norm_nonneg S) (Real.sqrt_nonneg (1 / 2))).mpr hS
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hs
  exact hn.trans hs

theorem hilbertSourceResolvent_one_sub_isUnit (S : E →L[ℂ] H) (hS : ‖S‖ ≤ Real.sqrt (1 / 2)) :
    IsUnit (1 - hilbertSourceResolvent S) :=
  isUnit_one_sub_of_norm_lt_one ((hilbertSourceResolvent_norm S hS).trans_lt (by norm_num))

theorem hilbertSourceUnshifted_variational (S : E →L[ℂ] H) (hS : ‖S‖ ≤ Real.sqrt (1 / 2))
    (f : H) (v : E) :
    inner ℂ (hilbertSourceUnshifted S f) v -
      inner ℂ (S (hilbertSourceUnshifted S f)) (S v) = inner ℂ f (S v) := by
  let q := (Ring.inverse (1 - hilbertSourceResolvent S)) f
  have hp := congrArg (fun T : H →L[ℂ] H => T f)
    (Ring.mul_inverse_cancel (1 - hilbertSourceResolvent S) (hilbertSourceResolvent_one_sub_isUnit S hS))
  change q - hilbertSourceResolvent S q = f at hp
  have hw : hilbertSourceUnshifted S f = S.adjoint q := rfl
  rw [hw, ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ q (S v) - inner ℂ (hilbertSourceResolvent S q) (S v) = _
  rw [← inner_sub_left, hp]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CoerciveHilbertSource
