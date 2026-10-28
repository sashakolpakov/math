import OAI.AlgebraicGeometry.Resolution.Blowups.ConstructedHomogenizedComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TransverseHypersurfaceCoordinates

/-! # Maximal Contact Coordinate Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MaximalContactCoordinateComparison.Construction

noncomputable section

/-! The comparison construction with the canonical partial derivatives of the étale charts. -/

universe u

variable {σ k R S C : Type u} [Field k] [CommRing R] [CommRing S] [Field C]
  [Algebra k R] [Algebra k S] [Algebra k C] [Algebra ℚ R] [Algebra ℚ S]
  [Algebra (MvPolynomial σ k) R] [Algebra (MvPolynomial σ k) S]
  [IsScalarTower k (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) S]
  [Algebra.Etale (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) S]
  [DecidableEq σ]

/-- Two tangent-ideal hypersurface coordinates with common complementary
coordinates have a constructed pointed common étale neighborhood on which their
homogenized ideals agree. The derivation frames are supplied by étaleness. -/
theorem exists_etale_maximal_contact_coordinate_comparison
    (e : R ≃ₐ[k] S) (J : Ideal R) (i : σ) (n : ℕ) (r : R →ₐ[k] C)
    (hcommon : ∀ a : σ, i ≠ a →
      e.symm (algebraMap (MvPolynomial σ k) S (MvPolynomial.X a)) =
        algebraMap (MvPolynomial σ k) R (MvPolynomial.X a))
    (hz : algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) ∈
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hw : e.symm (algebraMap (MvPolynomial σ k) S (MvPolynomial.X i)) ∈
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hpoint : r (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)) =
      r (e.symm (algebraMap (MvPolynomial σ k) S (MvPolynomial.X i)))) :
    ∃ (U : Type u) (_ : CommRing U) (_ : Algebra k U),
      ∃ f g : R →ₐ[k] U, ∃ v : U →ₐ[k] C,
        f.toRingHom.Etale ∧ g.toRingHom.Etale ∧
        (∀ p : MvPolynomial σ k,
          f (algebraMap (MvPolynomial σ k) R p) =
            g (e.symm (algebraMap (MvPolynomial σ k) S p))) ∧
        (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom =
          (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map g.toRingHom ∧
        (∀ x : R, v (f x) = r x) ∧ (∀ x : R, v (g x) = r x) := by
  exact ConstructedHomogenizedComparison.Construction.exists_pointed_etale_homogenized_comparison e
    (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i)
    (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := S) i) J i n r
    (Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X i) (Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X i) hcommon hz hw hpoint

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MaximalContactCoordinateComparison.Construction
