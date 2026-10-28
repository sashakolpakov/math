import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialFilteredAlgebra
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Homogeneous Filtered Image -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousFilteredImage.Dimension

noncomputable section

/-! If one coordinate is one, homogeneous degree-n images are the full degree filtration. -/

open _root_.MvPolynomial

variable {K B σ : Type*} [CommSemiring K] [CommSemiring B] [Algebra K B]

def homogenizeDegreeAt (i : σ) (n : ℕ) (p : MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ d ∈ p.support, monomial d (p.coeff d) * X i ^ (n - d.degree)

theorem homogenizeDegreeAt_homogeneous (i : σ) (n : ℕ) (p : MvPolynomial σ K)
    (hp : p.totalDegree ≤ n) : homogenizeDegreeAt i n p ∈ homogeneousSubmodule σ K n := by
  classical
  apply Submodule.sum_mem
  intro d hd
  have hdn : d.degree ≤ n := (MvPolynomial.le_totalDegree hd).trans hp
  have h := (isHomogeneous_monomial (d := d) (p.coeff d) rfl).mul
    (isHomogeneous_X_pow (R := K) i (n - d.degree))
  rw [Nat.add_sub_of_le hdn] at h
  exact (mem_homogeneousSubmodule _ _).mpr h

theorem aeval_homogenizeDegreeAt (v : σ → B) (i : σ) (hi : v i = 1)
    (n : ℕ) (p : MvPolynomial σ K) :
    aeval v (homogenizeDegreeAt i n p) = aeval v p := by
  classical
  rw [homogenizeDegreeAt, map_sum]
  simp only [map_mul, map_pow, aeval_X, hi, one_pow, mul_one]
  rw [← map_sum, ← p.as_sum]

theorem homogeneous_image_eq_polynomialFilteredPiece (v : σ → B) (i : σ)
    (hi : v i = 1) (n : ℕ) :
    (homogeneousSubmodule σ K n).map (aeval v).toLinearMap =
      PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n := by
  apply le_antisymm
  · rintro x ⟨p, hp, rfl⟩
    exact (PolynomialFilteredAlgebra.Dimension.mem_polynomialFilteredPiece v n _).mpr
      ⟨p, ((mem_homogeneousSubmodule _ _).mp hp).totalDegree_le, rfl⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := (PolynomialFilteredAlgebra.Dimension.mem_polynomialFilteredPiece v n x).mp hx
    exact ⟨homogenizeDegreeAt i n p, homogenizeDegreeAt_homogeneous i n p hp,
      aeval_homogenizeDegreeAt v i hi n p⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousFilteredImage.Dimension
