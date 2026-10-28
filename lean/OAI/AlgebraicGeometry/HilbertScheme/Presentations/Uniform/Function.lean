import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.Bound

/-! # Function -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.Function.GradedHilbert

noncomputable section

/-!
Saturated homogeneous ideals over arbitrary fields have Hilbert functions
among those of saturated monomial ideals over the rational numbers. This
gives a finite set of Hilbert functions and a uniform degree from which the
Hilbert function agrees with the prescribed Hilbert polynomial.
-/

open _root_.MvPolynomial

universe u

variable {K : Type u} [Field K] {n : ℕ}

theorem exists_rational_monomial_hilbertFunction (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))
    (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) :
    ∃ J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading ℚ n), SaturatedMonomialIdeals.GradedHilbert.IsMonomial J.toIdeal ∧ Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal ∧
      ∀ d : ℕ, Hilbert.Polynomial.GradedHilbert.hilbertFunction J.toIdeal d = Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d := by
  let L := RatFunc K
  let : Infinite L := Infinite.of_injective _ (RatFunc.algebraMap_injective K)
  let IE := ScalarExtension.GradedHilbert.scalarExtendedHomogeneousIdeal (L := L) I
  have hSatE : Hilbert.Polynomial.GradedHilbert.IsSaturated IE.toIdeal := ScalarExtension.GradedHilbert.scalarExtendedIdeal_isSaturated I.toIdeal hSat
  obtain ⟨l, hl, hl0, hreg⟩ := RegularLinearForm.GradedHilbert.exists_regular_linear_form IE hSatE
  obtain ⟨e, he⟩ := Linear.Changes.GradedHilbert.exists_coordinate_change l hl hl0
  let IC := InfiniteFieldBound.GradedHilbert.changedIdeal e IE
  have hregC : RegularInitialIdeal.GradedHilbert.VariableRegular IC.toIdeal 0 := by
    intro f hf
    apply hreg
    change Linear.Changes.GradedHilbert.extendLinearEquiv e (X 0 * f) ∈ IE.toIdeal at hf
    rw [map_mul, he] at hf
    exact hf
  let m := WeightedOrder.GradedHilbert.variableLastOrder (0 : Fin (n + 1))
  obtain ⟨S, hS⟩ := InitialIdeal.GradedHilbert.initialIdeal_isMonomial m IC.toIdeal
  have hSatS : Hilbert.Polynomial.GradedHilbert.IsSaturated (Hilbert.MonomialBasis.GradedHilbert.monomialSpan L S).toIdeal := by
    change Hilbert.Polynomial.GradedHilbert.IsSaturated (Ideal.span ((fun a => monomial a (1 : L)) '' S))
    rw [← hS]
    exact RegularInitialIdeal.GradedHilbert.initialIdeal_isSaturated 0 IC hregC
  refine ⟨Hilbert.MonomialBasis.GradedHilbert.monomialSpan ℚ S, ⟨S, rfl⟩,
    (MonomialBound.GradedHilbert.isSaturated_monomialSpan_field_independent (K := L) ℚ S).mp hSatS, ?_⟩
  intro d
  calc
    Hilbert.Polynomial.GradedHilbert.hilbertFunction (Hilbert.MonomialBasis.GradedHilbert.monomialSpan ℚ S).toIdeal d =
        Hilbert.Polynomial.GradedHilbert.hilbertFunction (Hilbert.MonomialBasis.GradedHilbert.monomialSpan L S).toIdeal d :=
      Hilbert.MonomialBasis.GradedHilbert.hilbertFunction_monomialSpan_field_independent L S d
    _ = Hilbert.Polynomial.GradedHilbert.hilbertFunction (InitialIdeal.GradedHilbert.initialIdeal m IC.toIdeal) d := by
      change Hilbert.Polynomial.GradedHilbert.hilbertFunction (Ideal.span ((fun a => monomial a (1 : L)) '' S)) d = _
      rw [← hS]
    _ = Hilbert.Polynomial.GradedHilbert.hilbertFunction IC.toIdeal d := InitialIdeal.GradedHilbert.hilbertFunction_initialIdeal m IC d
    _ = Hilbert.Polynomial.GradedHilbert.hilbertFunction IE.toIdeal d := InfiniteFieldBound.GradedHilbert.hilbertFunction_changedIdeal e IE d
    _ = Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d := Hilbert.ScalarExtension.GradedHilbert.hilbertFunction_scalarExtended I d

theorem exists_finite_uniform_hilbertFunctions (n : ℕ) (P : Polynomial ℚ) :
    ∃ F : Finset (ℕ → ℕ), ∀ (K : Type u) [Field K] (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)),
      Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal → Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P → Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal ∈ F := by
  classical
  let S := {J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading ℚ n) |
    SaturatedMonomialIdeals.GradedHilbert.IsMonomial J.toIdeal ∧ Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal ∧ Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial J.toIdeal P}
  have hS : S.Finite := SaturatedMonomialIdeals.GradedHilbert.finite_saturated_monomial_ideals n P
  refine ⟨hS.toFinset.image (fun J => Hilbert.Polynomial.GradedHilbert.hilbertFunction J.toIdeal), fun K _ I hSat hP => ?_⟩
  obtain ⟨J, hMon, hSatJ, hdim⟩ := exists_rational_monomial_hilbertFunction I hSat
  have hPJ : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial J.toIdeal P := by
    simpa only [Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial, hdim] using hP
  exact Finset.mem_image.mpr ⟨J, hS.mem_toFinset.mpr ⟨hMon, hSatJ, hPJ⟩, funext hdim⟩

/-- Uniform agreement with the Hilbert polynomial, valid over every field. -/
theorem exists_uniform_hilbertFunction_bound (n : ℕ) (P : Polynomial ℚ) :
    ∃ N : ℕ, ∀ (K : Type u) [Field K] (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)),
      Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal → Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P →
      ∀ d ≥ N, (Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d : ℚ) = P.eval (d : ℚ) := by
  classical
  let S := {J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading ℚ n) |
    SaturatedMonomialIdeals.GradedHilbert.IsMonomial J.toIdeal ∧ Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal ∧ Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial J.toIdeal P}
  have hS : S.Finite := SaturatedMonomialIdeals.GradedHilbert.finite_saturated_monomial_ideals n P
  let := hS.fintype
  choose b hb using fun J : S => J.property.2.2
  refine ⟨Finset.univ.sup b, fun K _ I hSat hP d hd => ?_⟩
  obtain ⟨J, hMon, hSatJ, hdim⟩ := exists_rational_monomial_hilbertFunction I hSat
  have hPJ : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial J.toIdeal P := by
    simpa only [Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial, hdim] using hP
  let J' : S := ⟨J, hMon, hSatJ, hPJ⟩
  rw [← hdim d]
  exact hb J' d ((Finset.le_sup (f := b) (Finset.mem_univ J')).trans hd)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.Function.GradedHilbert
