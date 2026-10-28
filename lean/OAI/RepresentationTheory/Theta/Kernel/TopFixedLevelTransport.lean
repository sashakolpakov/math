import OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedLevelTransport

/-! # Top Fixed Level Transport -/

namespace OAI.RepresentationTheory.Theta.Kernel.TopFixedLevelTransport.Intrinsic

noncomputable section

/-! Projection of the proved finite-level transport to actual native
ordinary top covectors. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedLevelTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {hd : d ≠ 0} {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}
variable {C C' : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2}
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P)
variable (D' : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C' P)
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)

theorem thetaTopForm_fixed_level
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (hψ : C'.ψ = C.ψ) (hu : Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd C D)
    (hG : Adelic.DataTheta.GeometryIdentification B) (hΘ : Adelic.DataTheta.Descent.ThetaConstruction B)
    (hCov : Adelic.DataTheta.Descent.RationalHeckeCovariance B P hd C' D')
    (g : Adelic.SpecialUnitary.SU H.val) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (hfix : Adelic.FiniteSchwartz.finiteAction F H K hd C P D (Adelic.RationalSU.rationalFiniteSU F H g) f = f) (z : Adelic.BallNatural.Ball) :
    (IntrinsicSecondProjection.Intrinsic.thetaTopForm B f (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)).compContinuousLinearMap
      (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage
        (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val) = IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z := by
  have ht := IntrinsicFixedLevelTransport.Intrinsic.geometricTensor_finite_action D D' B hns hH hK hψ hu hΘ g f hfix 2
  have he : IntrinsicSecondProjection.Intrinsic.thetaTopForm B (Adelic.FiniteSchwartz.finiteAction F H K hd C' P D' (Adelic.RationalSU.rationalFiniteSU F H g) f) = IntrinsicSecondProjection.Intrinsic.thetaTopForm B f := by
    funext w
    unfold IntrinsicSecondProjection.Intrinsic.thetaTopForm
    rw [ht]
  have hc := IntrinsicSecondAction.Intrinsic.thetaTopForm_covariance B P hd C' D' hG hCov g f z
  rw [he] at hc
  exact hc

end

end OAI.RepresentationTheory.Theta.Kernel.TopFixedLevelTransport.Intrinsic
