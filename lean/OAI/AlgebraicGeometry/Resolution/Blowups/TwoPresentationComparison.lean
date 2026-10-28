import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateCopy
import OAI.AlgebraicGeometry.Resolution.Blowups.MaximalContactCoordinateComparison

/-! # Two Presentation Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TwoPresentationComparison.Construction

noncomputable section

/-! Constructed homogenization comparison for two actual coordinate maps into one ring. -/

universe u

variable {σ k R C : Type u} [Field k] [CommRing R] [Field C]
  [Algebra k R] [Algebra k C] [Algebra ℚ R] [DecidableEq σ]

/-- Two specified étale presentations of the same ambient ring have a pointed
common étale comparison when their tangent-ideal hypersurface equations differ
and their complementary coordinates agree. -/
theorem exists_two_presentation_homogenized_comparison
    (α β : MvPolynomial σ k →ₐ[k] R) (hα : α.toRingHom.Etale) (hβ : β.toRingHom.Etale)
    (J : Ideal R) (i : σ) (n : ℕ) (r : R →ₐ[k] C)
    (hcommon : ∀ a : σ, i ≠ a → β (MvPolynomial.X a) = α (MvPolynomial.X a))
    (hz : α (MvPolynomial.X i) ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hw : β (MvPolynomial.X i) ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hpoint : r (α (MvPolynomial.X i)) = r (β (MvPolynomial.X i))) :
    ∃ (U : Type u) (_ : CommRing U) (_ : Algebra k U),
      ∃ f g : R →ₐ[k] U, ∃ v : U →ₐ[k] C,
        f.toRingHom.Etale ∧ g.toRingHom.Etale ∧
        (∀ p : MvPolynomial σ k, f (α p) = g (β p)) ∧
        (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom =
          (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map g.toRingHom ∧
        (∀ x : R, v (f x) = r x) ∧ (∀ x : R, v (g x) = r x) := by
  let P := MvPolynomial σ k
  let : Algebra P R := α.toRingHom.toAlgebra
  let : Algebra.Etale P R := hα
  let : IsScalarTower k P R := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap k R a = α (algebraMap k P a)
    exact (α.commutes a).symm)
  obtain ⟨S, instS, instkS, instPS, htor, hS, e, he⟩ :=
    Blowups.Etale.CoordinateCopy.Construction.exists_isomorphic_etale_coordinate_copy β hβ
  let : CommRing S := instS
  let : Algebra k S := instkS
  let : Algebra P S := instPS
  let : IsScalarTower k P S := htor
  let : Algebra.Etale P S := hS
  let : Algebra ℚ S := (e.toRingHom.comp (algebraMap ℚ R)).toAlgebra
  have he' : ∀ p : P, e.symm (algebraMap P S p) = β p := by
    intro p
    rw [he, e.symm_apply_apply]
  have hcommon' : ∀ a : σ, i ≠ a →
      e.symm (algebraMap P S (MvPolynomial.X a)) = algebraMap P R (MvPolynomial.X a) := by
    intro a hia
    rw [he']
    exact hcommon a hia
  have hw' : e.symm (algebraMap P S (MvPolynomial.X i)) ∈
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n := by rwa [he']
  have hpoint' : r (algebraMap P R (MvPolynomial.X i)) =
      r (e.symm (algebraMap P S (MvPolynomial.X i))) := by
    rw [he']
    exact hpoint
  obtain ⟨U, instU, instkU, f, g, v, hf, hg, hc, hH, hvf, hvg⟩ :=
    MaximalContactCoordinateComparison.Construction.exists_etale_maximal_contact_coordinate_comparison e J i n r hcommon' hz hw' hpoint'
  refine ⟨U, instU, instkU, f, g, v, hf, hg, ?_, hH, hvf, hvg⟩
  intro p
  have h := hc p
  change f (α p) = g (e.symm (algebraMap P S p)) at h
  rwa [he'] at h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TwoPresentationComparison.Construction
