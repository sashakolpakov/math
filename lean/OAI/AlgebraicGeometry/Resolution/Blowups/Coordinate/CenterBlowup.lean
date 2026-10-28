import OAI.AlgebraicGeometry.Resolution.Blowups.ChartLift
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Center Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterBlowup.Construction

noncomputable section

/-! Actual blowup charts for centers cut out by independent polynomial coordinates. -/

open _root_.MvPolynomial

universe u

variable {σ R : Type u} [CommRing R]

abbrev coordinateCenterElement (i : σ) : idealOfVars σ R :=
  ⟨X i, Ideal.subset_span ⟨i, rfl⟩⟩

abbrev coordinateCenterBlowupChart (i : σ) :=
  Blowup.Charts.Construction.blowupChart (idealOfVars σ R) (coordinateCenterElement (R := R) i)

/-- The standard coordinate substitution on the chart with denominator `X i`. -/
def coordinateBlowupSubstitution (i : σ) : MvPolynomial σ R →+* MvPolynomial σ R := by
  classical
  exact eval₂Hom C (fun j => if j = i then X i else X i * X j)

theorem coordinateBlowupSubstitution_C (i : σ) (r : R) :
    coordinateBlowupSubstitution i (C r) = C r := by
  classical
  simp [coordinateBlowupSubstitution]

theorem coordinateBlowupSubstitution_X_self (i : σ) :
    coordinateBlowupSubstitution (R := R) i (X i) = X i := by
  classical
  simp [coordinateBlowupSubstitution]

theorem coordinateBlowupSubstitution_X_ne (i j : σ) (hji : j ≠ i) :
    coordinateBlowupSubstitution (R := R) i (X j) = X i * X j := by
  classical
  simp [coordinateBlowupSubstitution, hji]

theorem coordinateBlowupSubstitution_center (i : σ) :
    (idealOfVars σ R).map (coordinateBlowupSubstitution i) = Ideal.span {X i} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro r ⟨j, rfl⟩
    change coordinateBlowupSubstitution i (X j) ∈ Ideal.span {X i}
    by_cases hji : j = i
    · subst j
      rw [coordinateBlowupSubstitution_X_self]
      exact Ideal.mem_span_singleton_self _
    · rw [coordinateBlowupSubstitution_X_ne i j hji]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_singleton_le_iff_mem]
    rw [← coordinateBlowupSubstitution_X_self (R := R) i]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)

/-- The actual chart maps to a polynomial ring through its universal property. -/
def coordinateBlowupToPolynomial (i : σ) : coordinateCenterBlowupChart (R := R) i →+* MvPolynomial σ R :=
  ChartLift.Construction.blowupChartLift (idealOfVars σ R) (coordinateCenterElement i) (coordinateBlowupSubstitution i)
    (by simpa only [coordinateCenterElement, coordinateBlowupSubstitution_X_self] using
      coordinateBlowupSubstitution_center (R := R) i)
    (by simpa only [coordinateCenterElement, coordinateBlowupSubstitution_X_self] using
      (isRegular_X (R := R) (n := i)))

theorem coordinateBlowupToPolynomial_constants (i : σ) (p : MvPolynomial σ R) :
    coordinateBlowupToPolynomial i (Blowup.Charts.Construction.blowupChartConstants (idealOfVars σ R) (coordinateCenterElement i) p) =
      coordinateBlowupSubstitution i p :=
  ChartLift.Construction.blowupChartLift_constants _ _ _ _ _ p

/-- The polynomial coordinates on the chart are its exceptional parameter
and the ratios of all the other center coordinates to that parameter. -/
def polynomialToCoordinateBlowup (i : σ) : MvPolynomial σ R →+* coordinateCenterBlowupChart (R := R) i := by
  classical
  exact eval₂Hom ((Blowup.Charts.Construction.blowupChartConstants (idealOfVars σ R) (coordinateCenterElement i)).comp C)
    (fun j => if j = i then Blowup.Charts.Construction.blowupChartConstants (idealOfVars σ R) (coordinateCenterElement i) (X i)
      else ExceptionalIdeal.Construction.blowupChartRatio (idealOfVars σ R) (coordinateCenterElement i) (coordinateCenterElement j))

theorem polynomialToCoordinateBlowup_C (i : σ) (r : R) :
    polynomialToCoordinateBlowup i (C r) =
      Blowup.Charts.Construction.blowupChartConstants (idealOfVars σ R) (coordinateCenterElement i) (C r) := by
  classical
  simp [polynomialToCoordinateBlowup]

theorem polynomialToCoordinateBlowup_X_self (i : σ) :
    polynomialToCoordinateBlowup (R := R) i (X i) =
      Blowup.Charts.Construction.blowupChartConstants (idealOfVars σ R) (coordinateCenterElement i) (X i) := by
  classical
  simp [polynomialToCoordinateBlowup]

theorem polynomialToCoordinateBlowup_X_ne (i j : σ) (hji : j ≠ i) :
    polynomialToCoordinateBlowup (R := R) i (X j) =
      ExceptionalIdeal.Construction.blowupChartRatio (idealOfVars σ R) (coordinateCenterElement i) (coordinateCenterElement j) := by
  classical
  simp [polynomialToCoordinateBlowup, hji]

theorem polynomialToCoordinateBlowup_substitution (i : σ) :
    (polynomialToCoordinateBlowup (R := R) i).comp (coordinateBlowupSubstitution i) =
      Blowup.Charts.Construction.blowupChartConstants (idealOfVars σ R) (coordinateCenterElement i) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, coordinateBlowupSubstitution_C, polynomialToCoordinateBlowup_C]
  · intro j
    rw [RingHom.comp_apply]
    by_cases hji : j = i
    · subst j
      rw [coordinateBlowupSubstitution_X_self, polynomialToCoordinateBlowup_X_self]
    · rw [coordinateBlowupSubstitution_X_ne i j hji, map_mul, polynomialToCoordinateBlowup_X_self,
        polynomialToCoordinateBlowup_X_ne i j hji]
      exact ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio (idealOfVars σ R) (coordinateCenterElement i) (coordinateCenterElement j)

theorem coordinateBlowupToPolynomial_ratio (i j : σ) (hji : j ≠ i) :
    coordinateBlowupToPolynomial (R := R) i
      (ExceptionalIdeal.Construction.blowupChartRatio (idealOfVars σ R) (coordinateCenterElement i) (coordinateCenterElement j)) = X j := by
  apply (isRegular_X (R := R) (n := i)).left
  have h := congrArg (coordinateBlowupToPolynomial (R := R) i)
    (ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio (idealOfVars σ R) (coordinateCenterElement i) (coordinateCenterElement j))
  simpa only [map_mul, coordinateBlowupToPolynomial_constants, coordinateCenterElement,
    coordinateBlowupSubstitution_X_self, coordinateBlowupSubstitution_X_ne i j hji] using h

theorem coordinateBlowupToPolynomial_fromPolynomial (i : σ) :
    (coordinateBlowupToPolynomial (R := R) i).comp (polynomialToCoordinateBlowup i) =
      RingHom.id (MvPolynomial σ R) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, polynomialToCoordinateBlowup_C,
      coordinateBlowupToPolynomial_constants, coordinateBlowupSubstitution_C]
    rfl
  · intro j
    rw [RingHom.comp_apply]
    by_cases hji : j = i
    · subst j
      rw [polynomialToCoordinateBlowup_X_self, coordinateBlowupToPolynomial_constants,
        coordinateBlowupSubstitution_X_self]
      rfl
    · rw [polynomialToCoordinateBlowup_X_ne i j hji, coordinateBlowupToPolynomial_ratio i j hji]
      rfl

theorem polynomialToCoordinateBlowup_toPolynomial (i : σ) :
    (polynomialToCoordinateBlowup (R := R) i).comp (coordinateBlowupToPolynomial i) =
      RingHom.id (coordinateCenterBlowupChart (R := R) i) := by
  apply ChartLift.Construction.blowupChart_hom_ext (idealOfVars σ R) (coordinateCenterElement i)
    (Blowup.Charts.Construction.blowupChartConstants (idealOfVars σ R) (coordinateCenterElement i))
    (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular _ _)
  · intro p
    rw [RingHom.comp_apply, coordinateBlowupToPolynomial_constants]
    exact congrArg (fun f : MvPolynomial σ R →+* coordinateCenterBlowupChart (R := R) i => f p)
      (polynomialToCoordinateBlowup_substitution i)
  · intro p
    rfl

/-- Each actual chart of the blowup of a coordinate center is an affine
space with the same number of coordinates as the original ambient space. -/
def coordinateCenterBlowupChartEquiv (i : σ) :
    coordinateCenterBlowupChart (R := R) i ≃+* MvPolynomial σ R :=
  RingEquiv.ofRingHom (coordinateBlowupToPolynomial i) (polynomialToCoordinateBlowup i)
    (coordinateBlowupToPolynomial_fromPolynomial i) (polynomialToCoordinateBlowup_toPolynomial i)

/-- The chart's coefficient algebra is the one induced by its actual base map. -/
abbrev coordinateCenterBlowupAlgebra (i : σ) : Algebra R (coordinateCenterBlowupChart (R := R) i) :=
  ((Blowup.Charts.Construction.blowupChartConstants (idealOfVars σ R) (coordinateCenterElement i)).comp C).toAlgebra

attribute [local instance] coordinateCenterBlowupAlgebra

/-- The explicit chart identification also preserves all base coefficients. -/
def coordinateCenterBlowupChartAlgEquiv (i : σ) :
    coordinateCenterBlowupChart (R := R) i ≃ₐ[R] MvPolynomial σ R where
  __ := coordinateCenterBlowupChartEquiv i
  commutes' r := (coordinateBlowupToPolynomial_constants i (C r)).trans (coordinateBlowupSubstitution_C i r)

/-- Blowup charts of a center generated by finitely many independent
coordinates are smooth over the coefficient ring. -/
theorem coordinateCenterBlowupChart_smooth [Finite σ] (i : σ) :
    Algebra.Smooth R (coordinateCenterBlowupChart (R := R) i) := by
  let : Algebra.Smooth R (MvPolynomial σ R) := ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.of_equiv (coordinateCenterBlowupChartAlgEquiv i).symm

/-- The actual affine chart morphism to the coefficient base is smooth. -/
theorem coordinateCenterBlowupChart_scheme_smooth [Finite σ] (i : σ) :
    AlgebraicGeometry.Smooth (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((Blowup.Charts.Construction.blowupChartConstants (idealOfVars σ R) (coordinateCenterElement i)).comp C))) := by
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)]
  exact (RingHom.smooth_algebraMap (R := R) (S := coordinateCenterBlowupChart (R := R) i)).mpr
    (coordinateCenterBlowupChart_smooth i)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterBlowup.Construction
