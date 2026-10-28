import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactDescent
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology

/-! # Intrinsic Origin Normalized Descent -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicOriginNormalizedDescent.Intrinsic

noncomputable section

/-! Origin normalization of actual native top forms preserves their
common finite level and geometric descent. The scalar is constant on
the ball and is taken from the actual native half frames. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise ContDiff

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactDescent.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicFamilyDescent.IntrinsicFamily OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}

def originNormalizedTop (B : Adelic.DataTheta.ComparisonData F H K A) (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A)
    (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p)) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (z : Adelic.BallNatural.Ball) : IntrinsicExterior.Intrinsic.TopCovector :=
  (Bp.halfFrame IntrinsicBallTopology.Intrinsic.origin / B.halfFrame IntrinsicBallTopology.Intrinsic.origin) • IntrinsicSecondProjection.Intrinsic.thetaTopForm Bp f z

theorem origin_normalized_top_smooth (B : Adelic.DataTheta.ComparisonData F H K A) (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A)
    (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p)) (hΘ : Adelic.DataTheta.Descent.ThetaConstruction Bp)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) : Adelic.BallGeometryData.BallSmooth (originNormalizedTop B p Bp f) := by
  have hs := IntrinsicSecondProjection.Intrinsic.thetaTopForm_smooth Bp hΘ f
  unfold Adelic.BallGeometryData.BallSmooth at hs ⊢
  have hc : ContDiffOn ℝ ⊤
      (fun _ : IntrinsicExterior.Intrinsic.Tangent => Bp.halfFrame IntrinsicBallTopology.Intrinsic.origin / B.halfFrame IntrinsicBallTopology.Intrinsic.origin) Adelic.BallGeometryData.ballDomain := contDiffOn_const
  have h : ContDiffOn ℝ ⊤
      (fun x => (Bp.halfFrame IntrinsicBallTopology.Intrinsic.origin / B.halfFrame IntrinsicBallTopology.Intrinsic.origin) •
        (if hx : x ∈ Adelic.BallGeometryData.ballDomain then IntrinsicSecondProjection.Intrinsic.thetaTopForm Bp f ⟨x,hx⟩ else 0)) Adelic.BallGeometryData.ballDomain :=
    hc.smul hs
  apply h.congr
  intro z hz
  simp [originNormalizedTop,hz]

variable {hd : d ≠ 0} {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}
variable (Q₀ : IntrinsicCompactChoices.Intrinsic.TotalWitnesses hd P A)
variable (Q : ∀ p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A, IntrinsicCompactChoices.Intrinsic.TotalWitnesses hd P (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))

theorem origin_normalized_top_invariant
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val)
    (hK : K.val.conjTranspose = -K.val) (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (h₀ : IntrinsicCompactChoices.Intrinsic.TotalValid Q₀ ψ) (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (hQ : IntrinsicCompactChoices.Intrinsic.TotalValid (Q p) ψ)
    (g : Adelic.SpecialUnitary.SU H.val) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (hfix : Adelic.FiniteSchwartz.finiteAction F H K hd Q₀.characters P Q₀.splittings (Adelic.RationalSU.rationalFiniteSU F H g) f = f)
    (z : Adelic.BallNatural.Ball) :
    (originNormalizedTop Q₀.comparison p (Q p).comparison f
      (Q₀.comparison.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)).compContinuousLinearMap
      (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage
        (Adelic.BallNatural.asSL (Q₀.comparison.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val) =
      originNormalizedTop Q₀.comparison p (Q p).comparison f z := by
  have h := IntrinsicCompactDescent.Intrinsic.compact_top_invariant Q₀ Q hns hH hK ψ h₀ p hQ g f hfix z
  ext a
  exact congrArg (fun eta : IntrinsicExterior.Intrinsic.TopCovector =>
    ((Q p).comparison.halfFrame IntrinsicBallTopology.Intrinsic.origin / Q₀.comparison.halfFrame IntrinsicBallTopology.Intrinsic.origin) * eta a) h

theorem origin_normalized_common_descent
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val)
    (hK : K.val.conjTranspose = -K.val) (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (h₀ : IntrinsicCompactChoices.Intrinsic.TotalValid Q₀ ψ) (hQ : ∀ p, IntrinsicCompactChoices.Intrinsic.TotalValid (Q p) ψ) :
    IntrinsicFamilyDescent.IntrinsicFamily.FamilyTopDescent Q₀.comparison P hd Q₀.characters Q₀.splittings
      (fun p f => originNormalizedTop Q₀.comparison p (Q p).comparison f) := by
  apply IntrinsicFamilyDescent.IntrinsicFamily.family_descent Q₀.comparison P hd Q₀.characters Q₀.splittings
    (fun p f => originNormalizedTop Q₀.comparison p (Q p).comparison f)
    h₀.2.2.2.2.2.2.2.2.2.2.2.2
  · intro p f
    exact origin_normalized_top_smooth Q₀.comparison p (Q p).comparison
      (hQ p).2.2.2.2.2.2.2.2.2.1 f
  · intro p g f hfix z
    exact origin_normalized_top_invariant Q₀ Q hns hH hK ψ h₀ p (hQ p) g f hfix z

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicOriginNormalizedDescent.Intrinsic
