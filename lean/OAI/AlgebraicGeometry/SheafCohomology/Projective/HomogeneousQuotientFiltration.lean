import OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousFilteredImage

/-! # Homogeneous Quotient Filtration -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousQuotientFiltration.Dimension

noncomputable section

/-! A surjective polynomial section map and an injective coefficient map identify the filtration. -/

open _root_.MvPolynomial

variable {K B σ E : Type*} [CommSemiring K] [CommSemiring B] [Algebra K B]
    [AddCommMonoid E] [Module K E]

def homogeneousQuotientFilteredEquiv (v : σ → B) (i : σ) (hi : v i = 1) (n : ℕ)
    (q : homogeneousSubmodule σ K n →ₗ[K] E) (hq : Function.Surjective q)
    (c : E →ₗ[K] B) (hc : Function.Injective c)
    (hcomp : ∀ p : homogeneousSubmodule σ K n, c (q p) = aeval v p.val) :
    E ≃ₗ[K] PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n := by
  have hmem (x : E) : c x ∈ PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n := by
    obtain ⟨p, rfl⟩ := hq x
    rw [hcomp]
    exact (PolynomialFilteredAlgebra.Dimension.mem_polynomialFilteredPiece v n _).mpr
      ⟨p.val, ((mem_homogeneousSubmodule _ _).mp p.property).totalDegree_le, rfl⟩
  apply LinearEquiv.ofBijective (c.codRestrict _ hmem)
  constructor
  · intro x y hxy
    exact hc (congrArg Subtype.val hxy)
  · intro x
    have hx : x.val ∈ (homogeneousSubmodule σ K n).map (aeval v).toLinearMap := by
      rw [HomogeneousFilteredImage.Dimension.homogeneous_image_eq_polynomialFilteredPiece v i hi n]
      exact x.property
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨q ⟨p, hp⟩, Subtype.ext ?_⟩
    exact (hcomp ⟨p, hp⟩).trans hpx

theorem adjoin_polynomial_generators_of_surjective (φ : MvPolynomial σ K →ₐ[K] B)
    (hφ : Function.Surjective φ) : Algebra.adjoin K (Set.range (fun i => φ (X i))) = ⊤ := by
  rw [← MvPolynomial.aeval_range]
  have he : MvPolynomial.aeval (fun i => φ (X i)) = φ := (MvPolynomial.aeval_unique φ).symm
  rw [he]
  exact (AlgHom.range_eq_top φ).mpr hφ

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousQuotientFiltration.Dimension
