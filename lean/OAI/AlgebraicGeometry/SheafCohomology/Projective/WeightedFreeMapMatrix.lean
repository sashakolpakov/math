import OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousPolynomialMatrix
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPieceFiniteness

/-! # Weighted Free Map Matrix -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.WeightedFreeMapMatrix

noncomputable section

/-! Polynomial matrices of homogeneous maps, including entries forced to vanish by degree. -/

open _root_.MvPolynomial
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] {r s : ℕ}
variable (d : Fin r → ℕ) (e : Fin s → ℕ)
variable (f : (Fin s →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (Fin r →₀ MvPolynomial σ R))
variable (hf : ∀ n x, x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading R (fun k => (e k : ℤ)) n →
  f x ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFreeGrading R (fun i => (d i : ℤ)) n)
include hf

omit [Fintype σ] in
theorem weightedFreeMapCoefficient_homogeneous (i : Fin r) (k : Fin s) :
    f (Finsupp.single k 1) i ∈ HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading R ((e k : ℤ) - (d i : ℤ)) :=
  (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.mem_weightedFreeGrading R (fun i => (d i : ℤ)) (e k : ℤ) _).mp
    (hf (e k : ℤ) _ (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.weightedFree_single_homogeneous R (fun k => (e k : ℤ)) k)) i

theorem weightedFreeMapCoefficient_zero (i : Fin r) (k : Fin s) (h : e k < d i) :
    f (Finsupp.single k 1) i = 0 := by
  have hc := weightedFreeMapCoefficient_homogeneous d e f hf i k
  rw [GradedPieceFiniteness.polynomialIntegerGrading_eq_bot_of_neg R ((e k : ℤ) - (d i : ℤ)) (by omega)] at hc
  exact hc

def weightedFreeMapPolynomial (i : Fin r) (k : Fin s) :
    homogeneousSubmodule σ R (e k - d i) :=
  if h : d i ≤ e k then
    ⟨f (Finsupp.single k 1) i, by
      have hc := weightedFreeMapCoefficient_homogeneous d e f hf i k
      rw [← Int.natCast_sub h, HilbertScheme.Presentations.IntegerPolynomialGrading.GradedModules.polynomialIntegerGrading_nat] at hc
      exact hc⟩
  else 0

theorem weightedFreeMapPolynomial_val (i : Fin r) (k : Fin s) :
    (weightedFreeMapPolynomial d e f hf i k).val = f (Finsupp.single k 1) i := by
  by_cases h : d i ≤ e k
  · simp [weightedFreeMapPolynomial, h]
  · simp only [weightedFreeMapPolynomial, dite_eq_right h, Submodule.coe_zero]
    exact (weightedFreeMapCoefficient_zero d e f hf i k (lt_of_not_ge h)).symm

theorem homogeneousPolynomialMatrixMap_weightedFreeMapPolynomial :
    HomogeneousPolynomialMatrix.homogeneousPolynomialMatrixMap d e (weightedFreeMapPolynomial d e f hf) = f := by
  apply Finsupp.lhom_ext
  intro k a
  rw [HomogeneousPolynomialMatrix.homogeneousPolynomialMatrixMap, Finsupp.linearCombination_single]
  have hcol : HomogeneousPolynomialMatrix.homogeneousMatrixColumn d e (weightedFreeMapPolynomial d e f hf) k =
      f (Finsupp.single k 1) := by
    apply Finsupp.ext
    intro i
    exact weightedFreeMapPolynomial_val d e f hf i k
  rw [hcol, ← map_smul]
  congr 1
  simp

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.WeightedFreeMapMatrix
