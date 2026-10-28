import OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion
import OAI.RepresentationTheory.Theta.Adelic.PeriodHolomorphic

/-! # Local Period Holomorphic -/

namespace OAI.RepresentationTheory.Theta.Adelic.LocalPeriodHolomorphic

noncomputable section

/-! Holomorphic local Siegel periods in the actual real position
coordinates at every archimedean place. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.PeriodHolomorphic OAI.RepresentationTheory.Theta.Adelic.SiegelRestriction

variable {I J : Type} [Fintype I] [Fintype J]

theorem realCongruence_holomorphic (T : Matrix I J ℝ) :
    Differentiable ℂ (SiegelRestriction.realCongruence T) := by
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  simp only [SiegelRestriction.realCongruence, Matrix.mul_apply]
  fun_prop

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem localSiegelPeriod_holomorphic (v : Fin A.places) :
    BallGeometryData.BallHolomorphic (fun z => (LocalPositionInclusion.localSiegelPeriod A P v z).matrix) := by
  have h := (realCongruence_holomorphic (LocalPositionInclusion.realPositionColumn A v)).comp_differentiableOn
    (PeriodHolomorphic.period_matrix_holomorphic A P)
  apply h.congr
  intro z hz
  simp only [Function.comp_apply, dite_eq_left hz]
  rfl

end

end OAI.RepresentationTheory.Theta.Adelic.LocalPeriodHolomorphic
