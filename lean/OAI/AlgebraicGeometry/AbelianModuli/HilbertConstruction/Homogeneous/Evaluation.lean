import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation

/-! # Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Evaluation

noncomputable section

/-! Homogeneous polynomial evaluation under a common rescaling of projective coordinates. -/

open scoped BigOperators

universe u v

variable {R B : Type u} [CommRing R] [CommRing B] {ι : Type v}

/-- Rescaling every coordinate multiplies a homogeneous polynomial of degree d by the dth power. -/
theorem homogeneousEvaluation_scale (c : R →+* B) (x : ι → B) (a : B)
    (p : MvPolynomial ι R) (d : ℕ) (hp : p.IsHomogeneous d) :
    MvPolynomial.eval₂Hom c (fun i => a * x i) p = a ^ d * MvPolynomial.eval₂Hom c x p := by
  classical
  change MvPolynomial.eval₂ c (fun i => a * x i) p = a ^ d * MvPolynomial.eval₂ c x p
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← hp.degree_eq_sum_deg_support he]
  ring

/-- Normalizing coordinates by a unit scales a degree-d numerator by the inverse dth power. -/
theorem homogeneousEvaluation_normalize (c : R →+* B) (x : ι → B) (a : Bˣ)
    (p : MvPolynomial ι R) (d : ℕ) (hp : p.IsHomogeneous d) :
    MvPolynomial.eval₂Hom c (fun i => (↑a⁻¹ : B) * x i) p =
      (↑a⁻¹ : B) ^ d * MvPolynomial.eval₂Hom c x p :=
  homogeneousEvaluation_scale c x (↑a⁻¹ : B) p d hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Evaluation
