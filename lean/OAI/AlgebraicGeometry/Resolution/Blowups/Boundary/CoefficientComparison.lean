import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.CenterDescent

/-! # Coefficient Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientComparison.Construction

noncomputable section

/-! Constructed comparisons for coefficient induction and descent of its centers. -/

universe u

variable {σ k R C : Type u} [Field k] [CommRing R] [Field C]
  [Algebra k R] [Algebra k C] [Algebra ℚ R]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
  [IsScalarTower k (MvPolynomial σ k) R] [Fintype σ] [DecidableEq σ]

/-- The constructed boundary-preserving comparison identifies the actual
coefficient ideals of the homogenization. If coefficient induction produces
compatible permissible centers on this common hypersurface, their ambient
ideals agree on an actual neighborhood of the original point. -/
theorem exists_boundary_coefficient_comparison
    (J : Ideal R) (B : Finset σ) (i : σ) (hiB : i ∉ B) (z : R) (n : ℕ) (r : R →ₐ[k] C)
    (htrans : ∃ j : σ, j ∉ B ∧ r (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) j z) ≠ 0)
    (hi : algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) ∈
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hpoint : r (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)) = r z) :
    let x := algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)
    let H := Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n
    ∃ (U : Type u) (_ : CommRing U) (_ : Algebra k U),
      ∃ f g : R →ₐ[k] U, ∃ v : U →ₐ[k] C, ∃ heq : f x = g z,
        f.toRingHom.Etale ∧ g.toRingHom.Etale ∧
        (∀ b ∈ B,
          f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X b)) =
            g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X b))) ∧
        H.map f.toRingHom = H.map g.toRingHom ∧
        (∀ a : R, v (f a) = r a) ∧ (∀ a : R, v (g a) = r a) ∧
        (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom x (f x) rfl).Etale ∧
        (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap g.toRingHom z (f x) heq.symm).Etale ∧
        (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k x H (n + 1)).map
            (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom x (f x) rfl) =
          (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z H (n + 1)).map
            (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap g.toRingHom z (f x) heq.symm) ∧
        ∀ I L : Ideal R, J ≤ I ^ (n + 1) → J ≤ L ^ (n + 1) → I.FG → L.FG →
          (I.map (Ideal.Quotient.mk (Ideal.span {x}))).map
              (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom x (f x) rfl) =
            (L.map (Ideal.Quotient.mk (Ideal.span {z}))).map
              (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap g.toRingHom z (f x) heq.symm) →
          ∃ s : R, r s ≠ 0 ∧ I.map (algebraMap R (Localization.Away s)) =
            L.map (algebraMap R (Localization.Away s)) := by
  dsimp only
  obtain ⟨U, instU, instkU, f, g, v, hf, hg, heq, hB, hH, hvf, hvg, hcenters⟩ :=
    CenterComparison.Construction.exists_boundary_transverse_center_comparison J B i hiB z n r htrans hi hz hpoint
  refine ⟨U, instU, instkU, f, g, v, heq, hf, hg, hB, hH, hvf, hvg,
    Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap_etale f.toRingHom hf _ _ rfl,
    Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap_etale g.toRingHom hg _ _ heq.symm, ?_, ?_⟩
  · exact Blowups.Etale.QuotientNaturality.Construction.relativeCoefficientIdeal_comparison_eq (σ := σ) f g hf hg _ z heq _ _ hH (n + 1)
  · intro I L hI hL hIfg hLfg hcoeff
    exact Coefficient.CenterDescent.Construction.pointed_hypersurface_center_descent f g hf v r hvf _ z heq I L
      (Blowups.Ideal.ImageCongruence.Construction.relative_tangent_le_permissible_center k J I n hI hi)
      (Blowups.Ideal.ImageCongruence.Construction.relative_tangent_le_permissible_center k J L n hL hz) hIfg hLfg hcoeff
      (hcenters L hL)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientComparison.Construction
