import OAI.RepresentationTheory.Theta.Kernel.IntrinsicFamilyDescent
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth

/-! # Intrinsic Level Smooth Top -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicLevelSmoothTop.Intrinsic

noncomputable section

/-! Smooth top sections at one actual principal level. The topology is
uniform convergence of all derivatives on compact subsets in the ball
chart; invariant pullbacks descend to the actual geometric top bundle. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicSections OAI.RepresentationTheory.Theta.Kernel.IntrinsicFamilyDescent.IntrinsicFamily
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondDescent.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)

def LevelInvariant (N : ℕ) (s : IntrinsicSmooth.IntrinsicSections.SmoothSection IntrinsicExterior.Intrinsic.TopCovector) : Prop :=
  ∀ g : Adelic.SpecialUnitary.SU H.val, Adelic.BallGeometryData.PrincipalLevel N g → ∀ z : Adelic.BallNatural.Ball,
    (s.value (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g) • z)).compContinuousLinearMap
      (fderiv ℂ (Adelic.DeterminantCoordinates.chartImage
        (Adelic.BallNatural.asSL (B.ball (Adelic.RationalSU.rationalArchimedeanSU F H g)))) z.val) = s.value z

abbrev LevelSmoothTop (N : ℕ) := {s : IntrinsicSmooth.IntrinsicSections.SmoothSection IntrinsicExterior.Intrinsic.TopCovector // LevelInvariant B N s}

theorem level_smooth_top_descends (N : ℕ) (s : LevelSmoothTop B N)
    (R : Setoid Adelic.BallNatural.Ball) (hR : ∀ z w, R.r z w ↔ Adelic.DataTheta.Descent.BallOrbit B N z w) :
    ∃ descended : Quotient R → IntrinsicSecondDescent.Intrinsic.TopBundle B N,
      Continuous descended ∧ (∀ q, IntrinsicSecondDescent.Intrinsic.topProjection B N R hR (descended q) = q) ∧
        ∀ z, descended (Quotient.mk R z) = Quot.mk (IntrinsicSecondDescent.Intrinsic.TopOrbit B N) (z,s.val.value z) :=
  IntrinsicFamilyDescent.IntrinsicFamily.native_smooth_top_section B N R hR s.val.value s.val.smooth s.property

theorem level_family_continuous {T : Type} [TopologicalSpace T] (N : ℕ)
    (s : T → IntrinsicSmooth.IntrinsicSections.SmoothSection IntrinsicExterior.Intrinsic.TopCovector) (hs : Continuous s) (hi : ∀ p, LevelInvariant B N (s p)) :
    Continuous (fun p => (⟨s p,hi p⟩ : LevelSmoothTop B N)) :=
  hs.subtype_mk hi

theorem level_derivative_continuous (N n : ℕ) :
    Continuous (fun s : LevelSmoothTop B N => IntrinsicSmooth.IntrinsicSections.derivative IntrinsicExterior.Intrinsic.TopCovector s.val n) :=
  (IntrinsicSmooth.IntrinsicSections.derivative_continuous IntrinsicExterior.Intrinsic.TopCovector n).comp continuous_subtype_val

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicLevelSmoothTop.Intrinsic
