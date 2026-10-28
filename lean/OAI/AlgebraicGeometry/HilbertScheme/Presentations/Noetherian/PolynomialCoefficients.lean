import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.SingleDegreeEquations
import Mathlib.RingTheory.Adjoin.FG

/-! # Polynomial Coefficients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.PolynomialCoefficients.GradedHilbert

noncomputable section

/-! A finite polynomial list over a base algebra is defined over its actual
finitely generated coefficient subalgebra, with homogeneity preserved.
Over a noetherian base the coefficient algebra is noetherian. -/

open _root_.AlgebraicGeometry _root_.MvPolynomial

universe u v w
variable {R : Type u} [CommRing R] {n : ℕ} {ι : Type w} [Fintype ι]
variable (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)

def polynomialCoefficientSet : Finset R := by
  classical
  exact Finset.univ.biUnion (fun j => (g j).coeffs)

variable (B : Type v) [CommRing B] [Algebra B R]

def polynomialCoefficientRing : Subalgebra B R := Algebra.adjoin B (↑(polynomialCoefficientSet g) : Set R)

instance polynomialCoefficientRing_finiteType : Algebra.FiniteType B (polynomialCoefficientRing g B) :=
  (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)

instance polynomialCoefficientRing_isNoetherian [IsNoetherianRing B] : IsNoetherianRing (polynomialCoefficientRing g B) :=
  Algebra.FiniteType.isNoetherianRing B _

theorem polynomial_coefficients_in_ring (j : ι) :
    ((g j).coeffs : Set R) ⊆ Set.range (polynomialCoefficientRing g B).val.toRingHom := by
  classical
  intro r hr
  refine ⟨⟨r, ?_⟩, rfl⟩
  apply Algebra.subset_adjoin
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hr⟩

theorem exists_polynomial_over_coefficient_ring (j : ι) :
    ∃ p : Hilbert.Polynomial.GradedHilbert.CoordinateRing (polynomialCoefficientRing g B) n,
      MvPolynomial.map (polynomialCoefficientRing g B).val.toRingHom p = g j :=
  MvPolynomial.mem_range_map_iff_coeffs_subset.mpr (polynomial_coefficients_in_ring g B j)

def polynomialOverCoefficientRing (j : ι) : Hilbert.Polynomial.GradedHilbert.CoordinateRing (polynomialCoefficientRing g B) n :=
  Classical.choose (exists_polynomial_over_coefficient_ring g B j)

theorem polynomialOverCoefficientRing_map (j : ι) :
    MvPolynomial.map (polynomialCoefficientRing g B).val.toRingHom (polynomialOverCoefficientRing g B j) = g j :=
  Classical.choose_spec (exists_polynomial_over_coefficient_ring g B j)

theorem polynomialOverCoefficientRing_homogeneous (N : ℕ) (hg : ∀ j, (g j).IsHomogeneous N) (j : ι) :
    (polynomialOverCoefficientRing g B j).IsHomogeneous N := by
  apply MvPolynomial.IsHomogeneous.of_map (f := (polynomialCoefficientRing g B).val.toRingHom) Subtype.val_injective
  rw [polynomialOverCoefficientRing_map]
  exact hg j

theorem coefficientRing_generatorsIdeal_map (N : ℕ) (hg : ∀ j, (g j).IsHomogeneous N) :
    (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (polynomialOverCoefficientRing g B) N
      (polynomialOverCoefficientRing_homogeneous g B N hg)).map
        (Graded.BaseChange.GradedHilbert.gradedCoefficientMap (polynomialCoefficientRing g B).val.toRingHom) = Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg := by
  apply HomogeneousIdeal.ext
  change Ideal.map (MvPolynomial.map (polynomialCoefficientRing g B).val.toRingHom)
    (Ideal.span (Set.range (polynomialOverCoefficientRing g B))) = Ideal.span (Set.range g)
  rw [Ideal.map_span, ← Set.range_comp]
  congr 2
  funext j
  exact polynomialOverCoefficientRing_map g B j

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.PolynomialCoefficients.GradedHilbert
