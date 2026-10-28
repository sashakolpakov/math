import OAI.AlgebraicGeometry.Resolution.Blowups.NonzeroPartialHomogenizedComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.TangentCongruentComparisonRefinement

/-! # Nonzero Partial Tangent Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.NonzeroPartialTangentComparison.Construction

noncomputable section

/-! A constructed transverse comparison retains tangent congruence for every later blowup. -/

universe u

variable {σ k R C : Type u} [Field k] [CommRing R] [Field C]
  [Algebra k R] [Algebra k C] [Algebra ℚ R]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
  [IsScalarTower k (MvPolynomial σ k) R] [Fintype σ] [DecidableEq σ]

theorem exists_nonzero_partial_tangent_comparison
    (J : Ideal R) (i : σ) (z : R) (n : ℕ) (r : R →ₐ[k] C)
    (hpartial : r (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i z) ≠ 0)
    (hi : algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) ∈
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hpoint : r (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)) = r z) :
    ∃ (U : Type u) (_ : CommRing U) (_ : Algebra k U),
      ∃ f g : R →ₐ[k] U, ∃ v : U →ₐ[k] C,
        f.toRingHom.Etale ∧ g.toRingHom.Etale ∧
        f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)) = g z ∧
        (∀ j : σ, i ≠ j →
          f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) =
            g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j))) ∧
        (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom =
          (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map g.toRingHom ∧
        (∀ x : R, v (f x) = r x) ∧ (∀ x : R, v (g x) = r x) ∧
        (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom =
          (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map g.toRingHom ∧
        (∀ x : R, g x - f x ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom) ∧
        ∀ I : Ideal R, J ≤ I ^ (n + 1) → I.map f.toRingHom = I.map g.toRingHom := by
  obtain ⟨A, instA, instkA, f, g, v, hf, hg, heq, hcomp, hH, hvf, hvg⟩ :=
    NonzeroPartialHomogenizedComparison.Construction.exists_etale_homogenized_comparison_of_nonzero_partial J i z n r hpartial hi hz hpoint
  let : CommRing A := instA
  let : Algebra k A := instkA
  obtain ⟨U, instU, instkU, η, v', hη, hvlift, hT, hdiff, hcenters⟩ :=
    TangentCongruentComparisonRefinement.Construction.refine_etale_comparison_with_tangent_congruence f g v hf hg J i z n hH heq hcomp hi hz
      (fun x => (hvf x).trans (hvg x).symm)
  let F := η.comp f
  let G := η.comp g
  have hF : F.toRingHom = η.toRingHom.comp f.toRingHom := by
    ext x
    rfl
  have hG : G.toRingHom = η.toRingHom.comp g.toRingHom := by
    ext x
    rfl
  refine ⟨U, instU, instkU, F, G, v', ?_, ?_, ?_, ?_, ?_, ?_, ?_, hT, hdiff, ?_⟩
  · rw [hF]
    exact RingHom.Etale.stableUnderComposition f.toRingHom η.toRingHom hf hη
  · rw [hG]
    exact RingHom.Etale.stableUnderComposition g.toRingHom η.toRingHom hg hη
  · exact congrArg η heq
  · intro j hij
    exact congrArg η (hcomp j hij)
  · rw [hF, hG, ← Ideal.map_map, ← Ideal.map_map, hH]
  · intro x
    exact (hvlift (f x)).trans (hvf x)
  · intro x
    exact (hvlift (g x)).trans (hvg x)
  · intro I hI
    rw [hF, hG, ← Ideal.map_map, ← Ideal.map_map]
    exact hcenters I hI

end

end OAI.AlgebraicGeometry.Resolution.Blowups.NonzeroPartialTangentComparison.Construction
