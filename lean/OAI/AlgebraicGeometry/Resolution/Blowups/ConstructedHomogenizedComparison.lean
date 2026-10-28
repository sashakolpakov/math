import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicCoordinateHomogenization

/-! # Constructed Homogenized Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ConstructedHomogenizedComparison.Construction

noncomputable section

/-! Constructing a pointed common étale neighborhood with equal homogenized ideals. -/

open scoped TensorProduct

universe u

variable {σ k R S C : Type u} [CommRing k] [CommRing R] [CommRing S] [Field C]
  [Algebra k R] [Algebra k S] [Algebra k C] [Algebra ℚ R] [Algebra ℚ S]
  [Algebra (MvPolynomial σ k) R] [Algebra (MvPolynomial σ k) S]
  [IsScalarTower k (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) S]
  [Algebra.Etale (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) S]
  [DecidableEq σ]

/-- Given two étale hypersurface coordinate systems with the same complementary
coordinates and tangent-ideal hypersurface equations, construct the common
étale neighborhood, the common point, and equality of the homogenized ideals. -/
theorem exists_pointed_etale_homogenized_comparison
    (e : R ≃ₐ[k] S) (D : Derivation k R R) (E : Derivation k S S)
    (J : Ideal R) (i : σ) (n : ℕ) (r : R →ₐ[k] C)
    (hD : ∀ a : σ, D (algebraMap (MvPolynomial σ k) R (MvPolynomial.X a)) =
      if i = a then 1 else 0)
    (hE : ∀ a : σ, E (algebraMap (MvPolynomial σ k) S (MvPolynomial.X a)) =
      if i = a then 1 else 0)
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
  let P := MvPolynomial σ k
  let α := IsScalarTower.toAlgHom k P R
  let β := IsScalarTower.toAlgHom k P S
  have hp : ∀ p : P, r (algebraMap P R p) = r (e.symm (algebraMap P S p)) := by
    have he : r.comp α = (r.comp e.symm.toAlgHom).comp β := by
      apply MvPolynomial.algHom_ext
      intro a
      change r (algebraMap P R (MvPolynomial.X a)) =
        r (e.symm (algebraMap P S (MvPolynomial.X a)))
      by_cases hia : i = a
      · subst a
        exact hpoint
      · rw [hcommon a hia]
    exact fun p => AlgHom.congr_fun he p
  obtain ⟨f, g, v, hf, hg, hcoords, hvf, hvg⟩ := Pointed.EtaleComparison.Construction.exists_pointed_etale_comparison e r hp
  let q : Ideal (R ⊗[P] S) := RingHom.ker v.toRingHom
  let : q.IsPrime := Ideal.comap_isPrime v.toRingHom ⊥
  have hq : ∀ x : R, g x - f x ∈ q := by
    intro x
    change v (g x - f x) = 0
    rw [map_sub, hvg, hvf, sub_self]
  obtain ⟨s, hs, heq⟩ := IsomorphicCoordinateHomogenization.Construction.isomorphic_coordinate_homogenization_neighborhood
    e D E f g J i n hD hE hcommon (fun a => hcoords (MvPolynomial.X a)) hz hw q hq
  let U := Localization.Away s
  let η : R ⊗[P] S →ₐ[k] U := IsScalarTower.toAlgHom k (R ⊗[P] S) U
  let f' := η.comp f
  let g' := η.comp g
  have hsunit : IsUnit (v s) := by
    apply isUnit_iff_ne_zero.mpr
    exact hs
  let v' : U →ₐ[k] C := IsLocalization.Away.liftAlgHom s hsunit
  have hη : η.toRingHom.Etale := by
    change (algebraMap (R ⊗[P] S) U).Etale
    exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway s)
  have hf' : f'.toRingHom = η.toRingHom.comp f.toRingHom := by
    ext x
    rfl
  have hg' : g'.toRingHom = η.toRingHom.comp g.toRingHom := by
    ext x
    rfl
  refine ⟨U, inferInstance, inferInstance, f', g', v', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf']
    exact RingHom.Etale.stableUnderComposition f.toRingHom η.toRingHom hf hη
  · rw [hg']
    exact RingHom.Etale.stableUnderComposition g.toRingHom η.toRingHom hg hη
  · intro p
    exact congrArg η (hcoords p)
  · rw [hf', hg']
    have hηmap : η.toRingHom = algebraMap (R ⊗[P] S) U := by
      apply RingHom.ext
      intro x
      rfl
    rw [hηmap, ← Ideal.map_map, ← Ideal.map_map]
    exact heq
  · intro x
    calc
      v' (f' x) = v (f x) := IsLocalization.Away.lift_eq s hsunit (f x)
      _ = r x := hvf x
  · intro x
    calc
      v' (g' x) = v (g x) := IsLocalization.Away.lift_eq s hsunit (g x)
      _ = r x := hvg x

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ConstructedHomogenizedComparison.Construction
