import OAI.RepresentationTheory.Theta.Kernel.IntrinsicChartFixedLevel
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLagrangianContinuity
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLevelSmoothTop

/-! # Intrinsic Lagrangian Fixed Level -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicLagrangianFixedLevel.Intrinsic

noncomputable section

/-! The actual compact Lagrangian family is continuous in C-infinity
inside the space of geometric top sections at a single native finite level. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSubspaces.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicNormalizedBase.IntrinsicCompactFamily
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLagrangianContinuity.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicChartFixedLevel.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLevelSmoothTop.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicSections OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicChartSections.IntrinsicNormalized OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {hd : d ≠ 0} {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (Q₀ : IntrinsicCompactChoices.Intrinsic.TotalWitnesses hd P A)
variable (Q : ∀ p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A, IntrinsicCompactChoices.Intrinsic.TotalWitnesses hd P (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (h₀ : IntrinsicCompactChoices.Intrinsic.TotalValid Q₀ ψ) (hQ : ∀ p, IntrinsicCompactChoices.Intrinsic.TotalValid (Q p) ψ)
variable (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))

def nativeLagrangianFamily (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) :
    IntrinsicCompactSubspaces.Intrinsic.CompactLagrangianChoice A → IntrinsicSmooth.IntrinsicSections.SmoothSection IntrinsicExterior.Intrinsic.TopCovector :=
  IntrinsicLagrangianContinuity.Intrinsic.lagrangianTopSection Q₀.comparison (fun p => (Q p).comparison)
    h₀.2.2.2.2.1 h₀.2.2.2.2.2.1
    (fun p => (hQ p).2.2.2.2.1) (fun p => (hQ p).2.2.2.2.2.1)
    h₀.2.2.2.2.2.2.2.2.2.1.1 hE f

theorem native_lagrangian_continuous (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) :
    Continuous (nativeLagrangianFamily Q₀ Q ψ h₀ hQ hE f) :=
  IntrinsicLagrangianContinuity.Intrinsic.lagrangian_top_continuous Q₀.comparison (fun p => (Q p).comparison)
    h₀.2.2.2.2.1 h₀.2.2.2.2.2.1
    (fun p => (hQ p).2.2.2.2.1) (fun p => (hQ p).2.2.2.2.2.1)
    h₀.2.2.2.2.2.2.2.2.2.1.1 hE f

theorem native_lagrangian_base (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (z : Adelic.BallNatural.Ball) :
    (nativeLagrangianFamily Q₀ Q ψ h₀ hQ hE f
      (Quotient.mk (IntrinsicCompactSubspaces.Intrinsic.compactSubspaceSetoid A) (IntrinsicCompactChoices.Intrinsic.identityChoice A))).value z =
        IntrinsicSecondProjection.Intrinsic.thetaTopForm Q₀.comparison f z :=
  IntrinsicLagrangianContinuity.Intrinsic.lagrangian_top_base Q₀.comparison (fun p => (Q p).comparison)
    h₀.2.2.2.2.1 h₀.2.2.2.2.2.1
    (fun p => (hQ p).2.2.2.2.1) (fun p => (hQ p).2.2.2.2.2.1)
    h₀.2.2.2.2.2.2.2.2.2.1.1 hE f z

variable (hns : ¬ IsSquare d) (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
variable (hArch : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) ψ)

include hns hH hK hArch in
theorem native_lagrangian_invariant (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (g : Adelic.SpecialUnitary.SU H.val)
    (hf : Adelic.FiniteSchwartz.finiteAction F H K hd Q₀.characters P Q₀.splittings (Adelic.RationalSU.rationalFiniteSU F H g) f = f)
    (p : IntrinsicCompactSubspaces.Intrinsic.CompactLagrangianChoice A) (z : Adelic.BallNatural.Ball) :
    ((nativeLagrangianFamily Q₀ Q ψ h₀ hQ hE f p).value
      (Q₀.comparison.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)).compContinuousLinearMap
        (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage
          (Adelic.BallNatural.asSL (Q₀.comparison.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val) =
      (nativeLagrangianFamily Q₀ Q ψ h₀ hQ hE f p).value z := by
  induction p using Quotient.inductionOn with
  | h p =>
    exact IntrinsicChartFixedLevel.Intrinsic.normalized_chart_top_invariant Q₀ p (Q p) hns hH hK ψ hArch h₀ (hQ p) hE g f hf z

def nativeLagrangianAtLevel (N : ℕ) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (hf : ∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g →
      Adelic.FiniteSchwartz.finiteAction F H K hd Q₀.characters P Q₀.splittings (Adelic.RationalSU.rationalFiniteSU F H g) f = f)
    (p : IntrinsicCompactSubspaces.Intrinsic.CompactLagrangianChoice A) : IntrinsicLevelSmoothTop.Intrinsic.LevelSmoothTop Q₀.comparison N :=
  ⟨nativeLagrangianFamily Q₀ Q ψ h₀ hQ hE f p,
    fun g hg z => native_lagrangian_invariant Q₀ Q ψ h₀ hQ hE hns hH hK hArch f g (hf g hg) p z⟩

theorem native_lagrangian_at_level_continuous (N : ℕ) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (hf : ∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g →
      Adelic.FiniteSchwartz.finiteAction F H K hd Q₀.characters P Q₀.splittings (Adelic.RationalSU.rationalFiniteSU F H g) f = f) :
    Continuous (nativeLagrangianAtLevel Q₀ Q ψ h₀ hQ hE hns hH hK hArch N f hf) :=
  (native_lagrangian_continuous Q₀ Q ψ h₀ hQ hE f).subtype_mk _

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicLagrangianFixedLevel.Intrinsic
