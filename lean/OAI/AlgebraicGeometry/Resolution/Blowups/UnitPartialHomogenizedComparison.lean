import OAI.AlgebraicGeometry.Resolution.Blowups.TwoPresentationComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateReplacement

/-! # Unit Partial Homogenized Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.UnitPartialHomogenizedComparison.Construction

noncomputable section

/-! Constructed comparison with any tangent-ideal equation transverse to a coordinate direction. -/

universe u

variable {σ k R C : Type u} [Field k] [CommRing R] [Field C]
  [Algebra k R] [Algebra k C] [Algebra ℚ R]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
  [IsScalarTower k (MvPolynomial σ k) R] [Fintype σ] [DecidableEq σ]

/-- The second coordinate presentation is constructed from the unit partial
derivative. The resulting pointed étale maps align the two hypersurfaces,
preserve all complementary coordinates, and identify the homogenized ideals. -/
theorem exists_etale_homogenized_comparison_of_unit_partial
    (J : Ideal R) (i : σ) (z : R) (n : ℕ) (r : R →ₐ[k] C)
    (hpartial : IsUnit (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i z))
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
        (∀ x : R, v (f x) = r x) ∧ (∀ x : R, v (g x) = r x) := by
  let x := algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)
  let α := Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap (K := k) i x
  let β := Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap (K := k) i z
  have hα : α.toRingHom.Etale := Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_etale i x (by
    change IsUnit (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i
      (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)))
    rw [Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X, ite_eq_left rfl]
    exact isUnit_one)
  have hβ : β.toRingHom.Etale := Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_etale i z hpartial
  have hcommon : ∀ a : Option {j : σ // i ≠ j}, none ≠ a →
      β (MvPolynomial.X a) = α (MvPolynomial.X a) := by
    intro a ha
    cases a with
    | none => exact False.elim (ha rfl)
    | some j =>
      exact (Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_some i z j).trans (Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_some i x j).symm
  have hαx : α (MvPolynomial.X none) ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n := by
    change Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap (K := k) i x (MvPolynomial.X none) ∈ _
    rw [Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_none]
    exact hi
  have hβz : β (MvPolynomial.X none) ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n := by
    change Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap (K := k) i z (MvPolynomial.X none) ∈ _
    rw [Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_none]
    exact hz
  have hp : r (α (MvPolynomial.X none)) = r (β (MvPolynomial.X none)) := by
    change r (Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap (K := k) i x (MvPolynomial.X none)) =
      r (Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap (K := k) i z (MvPolynomial.X none))
    rw [Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_none, Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_none]
    exact hpoint
  obtain ⟨U, instU, instkU, f, g, v, hf, hg, hc, hH, hvf, hvg⟩ :=
    TwoPresentationComparison.Construction.exists_two_presentation_homogenized_comparison α β hα hβ J none n r hcommon hαx hβz hp
  refine ⟨U, instU, instkU, f, g, v, hf, hg, ?_, ?_, hH, hvf, hvg⟩
  · have h := hc (MvPolynomial.X none)
    change f (Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap (K := k) i x (MvPolynomial.X none)) =
      g (Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap (K := k) i z (MvPolynomial.X none)) at h
    rwa [Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_none, Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_none] at h
  · intro j hij
    have h := hc (MvPolynomial.X (some ⟨j, hij⟩))
    change f (Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap (K := k) i x (MvPolynomial.X (some ⟨j, hij⟩))) =
      g (Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap (K := k) i z (MvPolynomial.X (some ⟨j, hij⟩))) at h
    rwa [Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_some, Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_some] at h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.UnitPartialHomogenizedComparison.Construction
