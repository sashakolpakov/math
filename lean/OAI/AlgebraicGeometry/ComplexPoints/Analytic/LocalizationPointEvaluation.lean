import OAI.AlgebraicGeometry.ComplexPoints.Analytic.Affine
import OAI.AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints
import Mathlib.Topology.Algebra.GroupWithZero

/-! # Localization Point Evaluation -/

namespace OAI.AlgebraicGeometry

/-!
# Continuity of fractions on principal affine open sets

The ambient topology is the ordinary evaluation topology on complex algebra
characters. Denominators are nonzero because the domain is the principal open
set on which the element being inverted does not vanish.
-/

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Fractions with a power denominator are continuous on the corresponding
principal open set of affine complex points. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_principalFraction (a g : A) (n : ℕ) :
    Continuous (fun x : {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A // x g ≠ 0} =>
      x.1 a / (x.1 g) ^ n) := by
  exact ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval a).comp continuous_subtype_val).div
    (((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval g).comp continuous_subtype_val).pow n)
    (fun x => pow_ne_zero n x.2)

/-- Every evaluation of the universal-property extension to a principal
localization varies continuously with the original complex point. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_localizePoint_eval (g : A) (z : Localization.Away g) :
    Continuous (fun x : {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A // x g ≠ 0} =>
      Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x.1 g x.2 z) := by
  simpa only [Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_eq_div_sec] using
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_principalFraction (IsLocalization.Away.sec g z).1 g
      (IsLocalization.Away.sec g z).2

/-- Extension of complex characters to a principal localization is continuous
for the ordinary evaluation topologies. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_localizePoint (g : A) :
    Continuous (fun x : {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A // x g ≠ 0} =>
      Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x.1 g x.2) := by
  apply (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff _).mpr
  exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_localizePoint_eval g

/-- The inverse algebraic localization-point equivalence is continuous. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_localizationPointEquiv_symm (g : A) :
    Continuous (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizationPointEquiv (K := ℂ) g).symm := by
  change Continuous (fun x : {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A // x g ≠ 0} =>
    Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint x.1 g x.2)
  exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_localizePoint g

end OAI.AlgebraicGeometry
