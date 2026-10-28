import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices
import OAI.RepresentationTheory.Theta.Kernel.TopFixedLevelTransport
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicFamilyDescent

/-! # Intrinsic Compact Descent -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactDescent.Intrinsic

noncomputable section

/-! All native compact-place choices descend on the original total
principal quotient. The finite level is selected once, before the
compact-place parameter is varied. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedLevelTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.TopFixedLevelTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicFamilyDescent.IntrinsicFamily
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondAction.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondDescent.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {hd : d ≠ 0} {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (Q₀ : IntrinsicCompactChoices.Intrinsic.TotalWitnesses hd P A)
variable (Q : ∀ p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A, IntrinsicCompactChoices.Intrinsic.TotalWitnesses hd P (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))

abbrev CommonCompactDescent :=
  IntrinsicFamilyDescent.IntrinsicFamily.FamilyTopDescent Q₀.comparison P hd Q₀.characters Q₀.splittings
    (fun p f => IntrinsicSecondProjection.Intrinsic.thetaTopForm (Q p).comparison f)

theorem compact_top_invariant
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val)
    (hK : K.val.conjTranspose = -K.val) (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (h₀ : IntrinsicCompactChoices.Intrinsic.TotalValid Q₀ ψ) (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (hQ : IntrinsicCompactChoices.Intrinsic.TotalValid (Q p) ψ)
    (g : Adelic.SpecialUnitary.SU H.val) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (hfix : Adelic.FiniteSchwartz.finiteAction F H K hd Q₀.characters P Q₀.splittings (Adelic.RationalSU.rationalFiniteSU F H g) f = f)
    (z : Adelic.BallNatural.Ball) :
    (IntrinsicSecondProjection.Intrinsic.thetaTopForm (Q p).comparison f (Q₀.comparison.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)).compContinuousLinearMap
      (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage
        (Adelic.BallNatural.asSL (Q₀.comparison.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val) =
          IntrinsicSecondProjection.Intrinsic.thetaTopForm (Q p).comparison f z := by
  obtain ⟨hψ₀,_,_,_,_,hG₀,_,_,hU₀,_,_,_,_⟩ := h₀
  obtain ⟨hψ,_,_,_,_,hG,_,_,_,hΘ,hCov,_,_⟩ := hQ
  have hball : (Q p).comparison.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) =
      Q₀.comparison.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) := by
    apply Subtype.ext
    apply Units.ext
    exact (hG.2.1 _).trans (hG₀.2.1 _).symm
  have hc := TopFixedLevelTransport.Intrinsic.thetaTopForm_fixed_level Q₀.splittings (Q p).splittings (Q p).comparison
    hns hH hK (hψ.trans hψ₀.symm) hU₀ hG hΘ hCov g f hfix z
  exact hball ▸ hc

theorem common_compact_descent
    (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val)
    (hK : K.val.conjTranspose = -K.val) (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (h₀ : IntrinsicCompactChoices.Intrinsic.TotalValid Q₀ ψ) (hQ : ∀ p, IntrinsicCompactChoices.Intrinsic.TotalValid (Q p) ψ)
    : CommonCompactDescent Q₀ Q := by
  have hbase := h₀
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hTop₀⟩ := hbase
  apply IntrinsicFamilyDescent.IntrinsicFamily.family_descent Q₀.comparison P hd Q₀.characters Q₀.splittings
    (fun p f => IntrinsicSecondProjection.Intrinsic.thetaTopForm (Q p).comparison f) hTop₀
  · intro p f
    have hparam := hQ p
    obtain ⟨_,_,_,_,_,_,_,_,_,hΘ,_,_,_⟩ := hparam
    exact IntrinsicSecondProjection.Intrinsic.thetaTopForm_smooth (Q p).comparison hΘ f
  · intro p g f hfix z
    exact compact_top_invariant Q₀ Q hns hH hK ψ h₀ p (hQ p) g f hfix z

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactDescent.Intrinsic
