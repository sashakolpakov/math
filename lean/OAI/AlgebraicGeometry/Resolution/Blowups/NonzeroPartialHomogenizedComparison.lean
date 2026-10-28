import OAI.AlgebraicGeometry.Resolution.Blowups.UnitPartialHomogenizedComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.HomogenizationBaseChange

/-! # Nonzero Partial Homogenized Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.NonzeroPartialHomogenizedComparison.Construction

noncomputable section

/-! Pointwise transversality is enough for a constructed local homogenization comparison. -/

universe u

variable {σ k R C : Type u} [Field k] [CommRing R] [Field C]
  [Algebra k R] [Algebra k C] [Algebra ℚ R]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
  [IsScalarTower k (MvPolynomial σ k) R] [Fintype σ] [DecidableEq σ]

/-- A nonzero partial derivative at the chosen point determines an actual
localization where the unit-partial comparison applies. Both resulting étale
maps are from the original ambient ring and preserve the original point. -/
theorem exists_etale_homogenized_comparison_of_nonzero_partial
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
        (∀ x : R, v (f x) = r x) ∧ (∀ x : R, v (g x) = r x) := by
  let d := Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i z
  let A := Localization.Away d
  let : Algebra.Etale R A := Algebra.Etale.of_isLocalizationAway d
  let : Algebra.Etale (MvPolynomial σ k) A := Algebra.Etale.comp (MvPolynomial σ k) R A
  let a : R →ₐ[k] A := IsScalarTower.toAlgHom k R A
  let J' := J.map a.toRingHom
  have hunit : IsUnit (r d) := isUnit_iff_ne_zero.mpr hpartial
  let r' : A →ₐ[k] C := IsLocalization.Away.liftAlgHom d hunit
  have hra : ∀ x : R, r' (a x) = r x := fun x => IsLocalization.Away.lift_eq d hunit x
  have hco : ∀ j : σ, algebraMap (MvPolynomial σ k) A (MvPolynomial.X j) =
      a (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) :=
    fun j => IsScalarTower.algebraMap_apply (MvPolynomial σ k) R A (MvPolynomial.X j)
  have hpart : IsUnit (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := A) i (a z)) := by
    change IsUnit (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := A) i (algebraMap R A z))
    rw [Blowups.Etale.RelativePartialBaseChange.Construction.etaleRelativePartial_baseChange (S := R) (T := A)]
    exact IsLocalization.Away.algebraMap_isUnit d
  have hδ : (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map a.toRingHom =
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J' n :=
    Relative.DifferentialBaseChange.Construction.etale_iteratedRelativeDifferentialIdeal_baseChange (σ := σ) J n
  have hi' : algebraMap (MvPolynomial σ k) A (MvPolynomial.X i) ∈
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J' n := by
    rw [hco, ← hδ]
    exact Ideal.mem_map_of_mem a.toRingHom hi
  have hz' : a z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J' n := by
    rw [← hδ]
    exact Ideal.mem_map_of_mem a.toRingHom hz
  have hp : r' (algebraMap (MvPolynomial σ k) A (MvPolynomial.X i)) = r' (a z) := by
    rw [hco, hra, hra]
    exact hpoint
  obtain ⟨U, instU, instkU, F, G, v, hF, hG, heq, hcomp, hH, hvF, hvG⟩ :=
    UnitPartialHomogenizedComparison.Construction.exists_etale_homogenized_comparison_of_unit_partial J' i (a z) n r' hpart hi' hz' hp
  let f := F.comp a
  let g := G.comp a
  have hf : f.toRingHom = F.toRingHom.comp a.toRingHom := by
    ext x
    rfl
  have hg : g.toRingHom = G.toRingHom.comp a.toRingHom := by
    ext x
    rfl
  have ha : a.toRingHom.Etale := RingHom.etale_algebraMap.mpr inferInstance
  have hHbase : (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map a.toRingHom =
      Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J' n := Relative.HomogenizationBaseChange.Construction.etale_relativeHomogenizedIdeal_baseChange (σ := σ) J n
  refine ⟨U, instU, instkU, f, g, v, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf]
    exact RingHom.Etale.stableUnderComposition a.toRingHom F.toRingHom ha hF
  · rw [hg]
    exact RingHom.Etale.stableUnderComposition a.toRingHom G.toRingHom ha hG
  · rw [hco] at heq
    exact heq
  · intro j hij
    have h := hcomp j hij
    rw [hco] at h
    exact h
  · rw [hf, hg, ← Ideal.map_map, ← Ideal.map_map, hHbase]
    exact hH
  · intro x
    exact (hvF (a x)).trans (hra x)
  · intro x
    exact (hvG (a x)).trans (hra x)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.NonzeroPartialHomogenizedComparison.Construction
