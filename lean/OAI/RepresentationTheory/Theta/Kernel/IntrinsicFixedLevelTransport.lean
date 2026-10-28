import OAI.RepresentationTheory.Theta.Kernel.IntrinsicArchimedeanIndependence
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondAction

/-! # Intrinsic Fixed Level Transport -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedLevelTransport.Intrinsic

noncomputable section

/-! A native construction with new archimedean coordinates inherits the
original finite stabilizer. This uses full AdelicTheta lift uniqueness and
rational theta invariance, rather than a parameter-dependent level. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicArchimedeanIndependence.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.IntrinsicTransport

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {hd : d ≠ 0} {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K}
variable {C C' : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m}
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)
variable (D' : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C' P)
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)

theorem completedTheta_finite_action
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val)
    (hK : K.val.conjTranspose = -K.val)
    (hψ : C'.ψ = C.ψ) (hu : Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd C D)
    (hΘ : Adelic.DataTheta.Descent.ThetaConstruction B) (g : Adelic.SpecialUnitary.SU H.val) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (hfix : Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f = f) (z : Adelic.BallNatural.Ball) :
    Adelic.DataTheta.completedTheta B (Adelic.FiniteSchwartz.finiteAction F H K hd C' P D' (Adelic.RationalSU.rationalFiniteSU F H g) f)
      (B.period z).matrix = Adelic.DataTheta.completedTheta B f (B.period z).matrix := by
  funext ξ
  have ht := IntrinsicArchimedeanIndependence.Intrinsic.finite_action_theta_independent F H K hd P C C' D D' hns hH hK hψ hu
    g (B.gaussian z ξ) f
  rw [hfix, ← hΘ.2.2.1, ← hΘ.2.2.1] at ht
  unfold Adelic.DataTheta.completedTheta
  rw [ht]

theorem geometricTensor_finite_action
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val)
    (hK : K.val.conjTranspose = -K.val)
    (hψ : C'.ψ = C.ψ) (hu : Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd C D)
    (hΘ : Adelic.DataTheta.Descent.ThetaConstruction B) (g : Adelic.SpecialUnitary.SU H.val) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (hfix : Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f = f) (a : ℕ) :
    Adelic.DataTheta.geometricTensor B (Adelic.FiniteSchwartz.finiteAction F H K hd C' P D' (Adelic.RationalSU.rationalFiniteSU F H g) f) a =
      Adelic.DataTheta.geometricTensor B f a := by
  funext z
  unfold Adelic.DataTheta.geometricTensor Adelic.DataTheta.completedTensor
  rw [completedTheta_finite_action D D' B hns hH hK hψ hu hΘ g f hfix z]

theorem geometricTensor_fixed_level
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val)
    (hK : K.val.conjTranspose = -K.val)
    (hψ : C'.ψ = C.ψ) (hu : Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd C D)
    (hΘ : Adelic.DataTheta.Descent.ThetaConstruction B) (hCov : Adelic.DataTheta.Descent.RationalHeckeCovariance B P hd C' D')
    (g : Adelic.SpecialUnitary.SU H.val) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (hfix : Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f = f) (a : ℕ) (z : Adelic.BallNatural.Ball) (v) :
    Adelic.DataTheta.geometricTensor B f a (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)
      (fun i => Adelic.BallGeometryData.dualFrameChange A (Adelic.RationalSU.rationalArchimedeanSU F H g) z (v i)) =
        Adelic.BallNatural.Factors.naturalHalfFactor m (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)) z * Adelic.DataTheta.geometricTensor B f a z v := by
  have h := (hCov g f).2.2.2 a z v
  change Adelic.DataTheta.geometricTensor B (Adelic.FiniteSchwartz.finiteAction F H K hd C' P D' (Adelic.RationalSU.rationalFiniteSU F H g) f) a
    (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)
      (fun i => Adelic.BallGeometryData.dualFrameChange A (Adelic.RationalSU.rationalArchimedeanSU F H g) z (v i)) = _ at h
  rw [geometricTensor_finite_action D D' B hns hH hK hψ hu hΘ g f hfix a] at h
  exact h

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedLevelTransport.Intrinsic
