import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.ChartModules
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.DegreeMapExactness

/-! # Cech Exactness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.CechExactness.GradedHilbert

noncomputable section

/-! Saturation preserves the full homogeneous Čech complex whenever it preserves the augmentation degree. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.DegreeMapExactness.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ)
variable (hdeg : Hilbert.Polynomial.GradedHilbert.degreeRelations (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal d = Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d)

include hdeg in
theorem saturationQuotientMap_homogeneous_eq_zero
    (m : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (hm : m ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (d : ℤ))
    (hz : ChartModules.GradedHilbert.saturationQuotientMap I m = 0) : m = 0 := by
  rw [Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading_nat] at hm
  obtain ⟨f, hf, rfl⟩ := hm
  have hsat : f ∈ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hmem : (⟨f, hf⟩ : Hilbert.Polynomial.GradedHilbert.grading R n d) ∈ Hilbert.Polynomial.GradedHilbert.degreeRelations (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal d := hsat
  rw [hdeg] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem

include hdeg in
theorem saturationChartMap_homogeneous_eq_zero (s : Finset (Fin (n + 1)))
    (x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) s)
    (hx : x ∈ Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s (d : ℤ))
    (hz : Localized.GradedExactness.GradedModules.awayModuleMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (ChartModules.GradedHilbert.saturationQuotientMap I) x = 0) : x = 0 := by
  by_cases hs : s.Nonempty
  · exact ChartModules.GradedHilbert.saturationChartMap_eq_zero I s hs x hz
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    obtain ⟨k, m, hm, hmx⟩ := (Localized.DegreePieces.GradedModules.mem_localizedDegreePiece_iff (WeightedFreeModules.GradedModules.polynomialIntegerGrading R)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (LaurentMonomials.ProjectiveCech.inversionMonomial R ∅) (∅ : Finset (Fin (n + 1))).card
      (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R ∅) (d : ℤ) x).mp hx
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] at hm
    rw [← hmx, Localized.GradedExactness.GradedModules.awayModuleMap_fraction] at hz
    obtain ⟨a, ha⟩ := (Module.Fractions.GradedModules.moduleFractionMap_eq_zero (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R ∅) k _).mp hz
    have hpm : ChartModules.GradedHilbert.saturationQuotientMap I m = 0 := by
      simpa only [Cech.AugmentationDegree.ProjectiveCech.inversionMonomial_empty, one_pow, one_smul] using ha
    have hm0 := saturationQuotientMap_homogeneous_eq_zero I d hdeg m hm hpm
    rw [← hmx, hm0, map_zero]

include hdeg in
theorem saturationCechDegreeMap_bijective (s : Finset (Fin (n + 1))) :
    Function.Bijective (Cech.DegreeMapExactness.ProjectiveCech.moduleCechDegreeMap R (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) (ChartModules.GradedHilbert.saturationQuotientMap I)
      (ChartModules.GradedHilbert.saturationQuotientMap_homogeneous I) (d : ℤ) s) := by
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    apply Subtype.ext
    apply saturationChartMap_homogeneous_eq_zero I d hdeg s (x - y).val (x - y).property
    have hz : Cech.DegreeMapExactness.ProjectiveCech.moduleCechDegreeMap R (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) (ChartModules.GradedHilbert.saturationQuotientMap I)
        (ChartModules.GradedHilbert.saturationQuotientMap_homogeneous I) (d : ℤ) s (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    exact congrArg Subtype.val hz
  · exact Localized.GradedExactness.GradedModules.localizedDegreeMap_surjective (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ)
      (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) (ChartModules.GradedHilbert.saturationQuotientMap I)
      (ChartModules.GradedHilbert.saturationQuotientMap_homogeneous I) (ChartModules.GradedHilbert.saturationQuotientMap_surjective I) (d : ℤ)

include hdeg in
theorem saturation_moduleCechExactAt_iff (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) q ↔
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) (d : ℤ) q :=
  Cech.DegreeMapExactness.ProjectiveCech.moduleCechExactAt_iff_of_degreeMap_bijective R (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
    (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) (ChartModules.GradedHilbert.saturationQuotientMap I)
    (ChartModules.GradedHilbert.saturationQuotientMap_homogeneous I) (d : ℤ) (saturationCechDegreeMap_bijective I d hdeg) q

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.CechExactness.GradedHilbert
