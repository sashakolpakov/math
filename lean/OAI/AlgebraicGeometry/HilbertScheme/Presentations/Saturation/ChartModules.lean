import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.VariablePowers
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualDegreeFlatness

/-! # Chart Modules -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.ChartModules.GradedHilbert

noncomputable section

/-! Projective saturation induces actual isomorphisms on every nonempty localized chart module, in every degree. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))

def saturationQuotientMap : (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) →ₗ[Hilbert.Polynomial.GradedHilbert.CoordinateRing R n]
    Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal :=
  (Ideal.Quotient.factorₐ (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (show I.toIdeal ≤ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal from
    Projective.Saturation.GradedHilbert.le_projectiveSaturation I)).toLinearMap

theorem saturationQuotientMap_surjective : Function.Surjective (saturationQuotientMap I) :=
  Ideal.Quotient.factor_surjective (show I.toIdeal ≤ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal from Projective.Saturation.GradedHilbert.le_projectiveSaturation I)

theorem saturationQuotientMap_homogeneous (d : ℤ)
    (x : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (hx : x ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I d) :
    saturationQuotientMap I x ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I) d := by
  obtain ⟨f, hf, rfl⟩ := hx
  exact ⟨f, hf, rfl⟩

theorem saturationChartMap_eq_zero (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) s)
    (hx : Localized.GradedExactness.GradedModules.awayModuleMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (saturationQuotientMap I) x = 0) : x = 0 := by
  obtain ⟨k, m, rfl⟩ := Module.Fractions.GradedModules.moduleFractionMap_surj (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [Localized.GradedExactness.GradedModules.awayModuleMap_fraction] at hx
  obtain ⟨l, hl⟩ := (Module.Fractions.GradedModules.moduleFractionMap_eq_zero (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) k _).mp hx
  have hmem : LaurentMonomials.ProjectiveCech.inversionMonomial R s ^ l * f ∈ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal :=
    Ideal.Quotient.eq_zero_iff_mem.mp hl
  obtain ⟨i, hi⟩ := hs
  obtain ⟨a, ha⟩ := VariablePowers.GradedHilbert.projectiveSaturation_variable_power I _ hmem i
  have he : LaurentMonomials.ProjectiveCech.inversionMonomial R s ^ (l + a) * f =
      LaurentMonomials.ProjectiveCech.inversionMonomial R (s.erase i) ^ a * (X i ^ a * (LaurentMonomials.ProjectiveCech.inversionMonomial R s ^ l * f)) := by
    rw [EventualDegreeFlatness.ProjectiveCech.inversionMonomial_factor_variable R s i hi]
    ring
  apply (Module.Fractions.GradedModules.moduleFractionMap_eq_zero (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) k _).mpr
  refine ⟨l + a, ?_⟩
  change Ideal.Quotient.mk I.toIdeal (LaurentMonomials.ProjectiveCech.inversionMonomial R s ^ (l + a) * f) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [he]
  exact I.toIdeal.mul_mem_left _ ha

theorem saturationChartMap_bijective (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    Function.Bijective (Localized.GradedExactness.GradedModules.awayModuleMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (saturationQuotientMap I)) := by
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    apply saturationChartMap_eq_zero I s hs
    rw [map_sub, hxy, sub_self]
  · exact Localized.GradedExactness.GradedModules.awayModuleMap_surjective _ _ (saturationQuotientMap_surjective I)

def saturationChartDegreeEquiv (s : Finset (Fin (n + 1))) (hs : s.Nonempty) (d : ℤ) :
    Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s d ≃ₗ[R]
      Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) s d :=
  LinearEquiv.ofBijective (Localized.GradedExactness.GradedModules.localizedDegreeMap (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
    (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ)
    (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) (saturationQuotientMap I) (saturationQuotientMap_homogeneous I) d)
    ⟨by
      intro x y hxy
      exact Subtype.ext ((saturationChartMap_bijective I s hs).1 (congrArg Subtype.val hxy)),
      Localized.GradedExactness.GradedModules.localizedDegreeMap_surjective (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ)
        (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) (saturationQuotientMap I)
        (saturationQuotientMap_homogeneous I) (saturationQuotientMap_surjective I) d⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.ChartModules.GradedHilbert
