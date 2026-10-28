import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.SubcenterMap
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Polynomial Line Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialLineBlowup.Construction

noncomputable section

/-! The blowup of a center in the zero section of a polynomial line. -/

open _root_.Polynomial

universe u

variable {H : Type u} [CommRing H]

theorem polynomial_constant_isRegular (c : H) (hc : IsRegular c) : IsRegular (C c) := by
  apply (Commute.isRegular_iff (fun p : H[X] => Commute.all (C c) p)).mpr
  intro p q hpq
  ext n
  apply hc.left
  simpa only [coeff_C_mul] using congrArg (fun f : H[X] => f.coeff n) hpq

def polynomialLineCenter (K : Ideal H) : Ideal H[X] :=
  K.map C ⊔ Ideal.span {X}

abbrev polynomialLineDenominator (K : Ideal H) (a : K) : polynomialLineCenter K :=
  Blowup.SubcenterMap.Construction.subcenterDenominator K (polynomialLineCenter K) C le_sup_left a

abbrev polynomialLineBlowupChart (K : Ideal H) (a : K) :=
  Blowup.Charts.Construction.blowupChart (polynomialLineCenter K) (polynomialLineDenominator K a)

def polynomialLineChartBaseMap (K : Ideal H) (a : K) :
    Blowup.Charts.Construction.blowupChart K a →+* polynomialLineBlowupChart K a :=
  Blowup.SubcenterMap.Construction.blowupSubcenterMap K (polynomialLineCenter K) C le_sup_left a

theorem polynomialLineChartBaseMap_constants (K : Ideal H) (a : K) (h : H) :
    polynomialLineChartBaseMap K a (Blowup.Charts.Construction.blowupChartConstants K a h) =
      Blowup.Charts.Construction.blowupChartConstants (polynomialLineCenter K) (polynomialLineDenominator K a) (C h) :=
  Blowup.SubcenterMap.Construction.blowupSubcenterMap_constants K (polynomialLineCenter K) C le_sup_left a h

/-- Substitute the exceptional parameter times the new line coordinate. -/
def polynomialLineChartSubstitution (K : Ideal H) (a : K) : H[X] →+* (Blowup.Charts.Construction.blowupChart K a)[X] :=
  Polynomial.eval₂RingHom (C.comp (Blowup.Charts.Construction.blowupChartConstants K a))
    (C (Blowup.Charts.Construction.blowupChartConstants K a a.val) * X)

theorem polynomialLineChartSubstitution_C (K : Ideal H) (a : K) (h : H) :
    polynomialLineChartSubstitution K a (C h) = C (Blowup.Charts.Construction.blowupChartConstants K a h) :=
  Polynomial.eval₂_C _ _

theorem polynomialLineChartSubstitution_X (K : Ideal H) (a : K) :
    polynomialLineChartSubstitution K a X = C (Blowup.Charts.Construction.blowupChartConstants K a a.val) * X :=
  Polynomial.eval₂_X _ _

theorem polynomialLineChartSubstitution_center (K : Ideal H) (a : K) :
    (polynomialLineCenter K).map (polynomialLineChartSubstitution K a) =
      Ideal.span {C (Blowup.Charts.Construction.blowupChartConstants K a a.val)} := by
  have hcomp : (polynomialLineChartSubstitution K a).comp C = C.comp (Blowup.Charts.Construction.blowupChartConstants K a) := by
    apply RingHom.ext
    exact polynomialLineChartSubstitution_C K a
  rw [polynomialLineCenter, Ideal.map_sup, Ideal.map_map, hcomp, ← Ideal.map_map,
    ExceptionalIdeal.Construction.blowupChart_extendedIdeal, Ideal.map_span, Set.image_singleton,
    Ideal.map_span, Set.image_singleton, polynomialLineChartSubstitution_X]
  apply sup_eq_left.mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨rfl⟩
  exact (Ideal.span {C (Blowup.Charts.Construction.blowupChartConstants K a a.val)}).mul_mem_right X
    (Ideal.mem_span_singleton_self _)

/-- The center becomes the regular principal exceptional ideal under substitution. -/
theorem polynomialLineChartSubstitution_principal (K : Ideal H) (a : K) :
    (polynomialLineCenter K).map (polynomialLineChartSubstitution K a) =
      Ideal.span {polynomialLineChartSubstitution K a (polynomialLineDenominator K a).val} := by
  change _ = Ideal.span {polynomialLineChartSubstitution K a (C a.val)}
  rw [polynomialLineChartSubstitution_C, polynomialLineChartSubstitution_center]

theorem polynomialLineChartSubstitution_regular (K : Ideal H) (a : K) :
    IsRegular (polynomialLineChartSubstitution K a (polynomialLineDenominator K a).val) := by
  change IsRegular (polynomialLineChartSubstitution K a (C a.val))
  rw [polynomialLineChartSubstitution_C]
  exact polynomial_constant_isRegular _ (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular K a)

/-- The chart map to the polynomial line over the hypersurface blowup chart. -/
def polynomialLineBlowupToPolynomial (K : Ideal H) (a : K) :
    polynomialLineBlowupChart K a →+* (Blowup.Charts.Construction.blowupChart K a)[X] :=
  ChartLift.Construction.blowupChartLift (polynomialLineCenter K) (polynomialLineDenominator K a)
    (polynomialLineChartSubstitution K a) (polynomialLineChartSubstitution_principal K a)
    (polynomialLineChartSubstitution_regular K a)

theorem polynomialLineBlowupToPolynomial_constants (K : Ideal H) (a : K) (p : H[X]) :
    polynomialLineBlowupToPolynomial K a
      (Blowup.Charts.Construction.blowupChartConstants (polynomialLineCenter K) (polynomialLineDenominator K a) p) =
        polynomialLineChartSubstitution K a p :=
  ChartLift.Construction.blowupChartLift_constants _ _ _ _ _ p

def polynomialLineNormalElement (K : Ideal H) : polynomialLineCenter K :=
  ⟨X, (le_sup_right : Ideal.span {(X : H[X])} ≤ polynomialLineCenter K)
    (Ideal.mem_span_singleton_self X)⟩

def polynomialLineDividedCoordinate (K : Ideal H) (a : K) : polynomialLineBlowupChart K a :=
  ExceptionalIdeal.Construction.blowupChartRatio (polynomialLineCenter K) (polynomialLineDenominator K a) (polynomialLineNormalElement K)

/-- Evaluate the new coordinate at the divided normal coordinate. -/
def polynomialLinePolynomialToBlowup (K : Ideal H) (a : K) :
    (Blowup.Charts.Construction.blowupChart K a)[X] →+* polynomialLineBlowupChart K a :=
  Polynomial.eval₂RingHom (polynomialLineChartBaseMap K a) (polynomialLineDividedCoordinate K a)

theorem polynomialLinePolynomialToBlowup_C (K : Ideal H) (a : K) (h : Blowup.Charts.Construction.blowupChart K a) :
    polynomialLinePolynomialToBlowup K a (C h) = polynomialLineChartBaseMap K a h :=
  Polynomial.eval₂_C _ _

theorem polynomialLinePolynomialToBlowup_X (K : Ideal H) (a : K) :
    polynomialLinePolynomialToBlowup K a X = polynomialLineDividedCoordinate K a :=
  Polynomial.eval₂_X _ _

theorem polynomialLineBlowupToPolynomial_base (K : Ideal H) (a : K) (x : Blowup.Charts.Construction.blowupChart K a) :
    polynomialLineBlowupToPolynomial K a (polynomialLineChartBaseMap K a x) = C x := by
  have he : (polynomialLineBlowupToPolynomial K a).comp (polynomialLineChartBaseMap K a) = C := by
    apply ChartLift.Construction.blowupChart_hom_ext K a (C.comp (Blowup.Charts.Construction.blowupChartConstants K a))
      (polynomial_constant_isRegular _ (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular K a))
    · intro h
      change polynomialLineBlowupToPolynomial K a
        (polynomialLineChartBaseMap K a (Blowup.Charts.Construction.blowupChartConstants K a h)) = C (Blowup.Charts.Construction.blowupChartConstants K a h)
      rw [polynomialLineChartBaseMap_constants,
        polynomialLineBlowupToPolynomial_constants, polynomialLineChartSubstitution_C]
    · intro h
      rfl
  exact RingHom.congr_fun he x

theorem polynomialLineBlowupToPolynomial_dividedCoordinate (K : Ideal H) (a : K) :
    polynomialLineBlowupToPolynomial K a (polynomialLineDividedCoordinate K a) = X := by
  have h := congrArg (polynomialLineBlowupToPolynomial K a)
    (ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio (polynomialLineCenter K) (polynomialLineDenominator K a)
      (polynomialLineNormalElement K))
  change polynomialLineBlowupToPolynomial K a
    (Blowup.Charts.Construction.blowupChartConstants (polynomialLineCenter K) (polynomialLineDenominator K a) (C a.val) *
      polynomialLineDividedCoordinate K a) =
    polynomialLineBlowupToPolynomial K a
      (Blowup.Charts.Construction.blowupChartConstants (polynomialLineCenter K) (polynomialLineDenominator K a) X) at h
  rw [map_mul, polynomialLineBlowupToPolynomial_constants, polynomialLineBlowupToPolynomial_constants,
    polynomialLineChartSubstitution_C, polynomialLineChartSubstitution_X] at h
  exact (polynomial_constant_isRegular _ (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular K a)).left h

theorem polynomialLinePolynomialToBlowup_substitution (K : Ideal H) (a : K) (p : H[X]) :
    polynomialLinePolynomialToBlowup K a (polynomialLineChartSubstitution K a p) =
      Blowup.Charts.Construction.blowupChartConstants (polynomialLineCenter K) (polynomialLineDenominator K a) p := by
  have he : (polynomialLinePolynomialToBlowup K a).comp (polynomialLineChartSubstitution K a) =
      Blowup.Charts.Construction.blowupChartConstants (polynomialLineCenter K) (polynomialLineDenominator K a) := by
    apply Polynomial.ringHom_ext
    · intro h
      change polynomialLinePolynomialToBlowup K a (polynomialLineChartSubstitution K a (C h)) = _
      rw [polynomialLineChartSubstitution_C, polynomialLinePolynomialToBlowup_C,
        polynomialLineChartBaseMap_constants]
    · change polynomialLinePolynomialToBlowup K a (polynomialLineChartSubstitution K a X) = _
      rw [polynomialLineChartSubstitution_X, map_mul, polynomialLinePolynomialToBlowup_C,
        polynomialLinePolynomialToBlowup_X, polynomialLineChartBaseMap_constants]
      exact ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio (polynomialLineCenter K) (polynomialLineDenominator K a)
        (polynomialLineNormalElement K)
  exact RingHom.congr_fun he p

theorem polynomialLineBlowup_inverse_left (K : Ideal H) (a : K) :
    (polynomialLinePolynomialToBlowup K a).comp (polynomialLineBlowupToPolynomial K a) =
      RingHom.id (polynomialLineBlowupChart K a) := by
  apply ChartLift.Construction.blowupChart_hom_ext (polynomialLineCenter K) (polynomialLineDenominator K a)
    (Blowup.Charts.Construction.blowupChartConstants (polynomialLineCenter K) (polynomialLineDenominator K a))
    (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular _ _)
  · intro p
    change polynomialLinePolynomialToBlowup K a (polynomialLineBlowupToPolynomial K a
      (Blowup.Charts.Construction.blowupChartConstants (polynomialLineCenter K) (polynomialLineDenominator K a) p)) = _
    rw [polynomialLineBlowupToPolynomial_constants, polynomialLinePolynomialToBlowup_substitution]
  · intro p
    rfl

theorem polynomialLineBlowup_inverse_right (K : Ideal H) (a : K) :
    (polynomialLineBlowupToPolynomial K a).comp (polynomialLinePolynomialToBlowup K a) =
      RingHom.id (Blowup.Charts.Construction.blowupChart K a)[X] := by
  apply Polynomial.ringHom_ext
  · intro x
    change polynomialLineBlowupToPolynomial K a (polynomialLinePolynomialToBlowup K a (C x)) = C x
    rw [polynomialLinePolynomialToBlowup_C, polynomialLineBlowupToPolynomial_base]
  · change polynomialLineBlowupToPolynomial K a (polynomialLinePolynomialToBlowup K a X) = X
    rw [polynomialLinePolynomialToBlowup_X, polynomialLineBlowupToPolynomial_dividedCoordinate]

/-- The actual ambient blowup chart is a polynomial line over the actual
hypersurface blowup chart, with its divided normal coordinate as variable. -/
def polynomialLineBlowupEquiv (K : Ideal H) (a : K) :
    polynomialLineBlowupChart K a ≃+* (Blowup.Charts.Construction.blowupChart K a)[X] where
  __ := polynomialLineBlowupToPolynomial K a
  invFun := polynomialLinePolynomialToBlowup K a
  left_inv x := RingHom.congr_fun (polynomialLineBlowup_inverse_left K a) x
  right_inv x := RingHom.congr_fun (polynomialLineBlowup_inverse_right K a) x

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialLineBlowup.Construction
