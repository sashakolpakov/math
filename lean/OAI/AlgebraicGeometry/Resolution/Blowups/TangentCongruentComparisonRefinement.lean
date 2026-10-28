import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.EtaleNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.ImageCongruence

/-! # Tangent Congruent Comparison Refinement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TangentCongruentComparisonRefinement.Construction

noncomputable section

/-! Retain the tangent-ideal congruence itself on a pointed comparison refinement, for propagation through later blowups. -/

universe u

variable {σ k R S C : Type u} [Field k] [CommRing R] [CommRing S] [Field C]
  [Algebra k R] [Algebra k S] [Algebra k C]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
  [IsScalarTower k (MvPolynomial σ k) R] [Fintype σ] [DecidableEq σ]

/-- A further pointed étale refinement makes the two comparison maps agree
on every permissible embedded center ideal, as required for gluing centers. -/
theorem refine_etale_comparison_with_tangent_congruence
    (f g : R →ₐ[k] S) (v : S →ₐ[k] C) (hf : f.toRingHom.Etale) (hg : g.toRingHom.Etale)
    (J : Ideal R) (i : σ) (z : R) (n : ℕ)
    (hH : (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom =
      (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map g.toRingHom)
    (heq : f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)) = g z)
    (hcomp : ∀ j : σ, i ≠ j →
      f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) =
        g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)))
    (hi : algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) ∈
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hv : ∀ x : R, v (f x) = v (g x)) :
    ∃ (U : Type u) (_ : CommRing U) (_ : Algebra k U),
      ∃ η : S →ₐ[k] U, ∃ v' : U →ₐ[k] C,
        η.toRingHom.Etale ∧ (∀ x : S, v' (η x) = v x) ∧
        (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (η.toRingHom.comp f.toRingHom) =
          (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (η.toRingHom.comp g.toRingHom) ∧
        (∀ x : R, (η.toRingHom.comp g.toRingHom) x - (η.toRingHom.comp f.toRingHom) x ∈
          (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (η.toRingHom.comp f.toRingHom)) ∧
        ∀ I : Ideal R, J ≤ I ^ (n + 1) →
          (I.map f.toRingHom).map η.toRingHom = (I.map g.toRingHom).map η.toRingHom := by
  let T := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
  let L := T.map f.toRingHom
  have hT : T.map f.toRingHom = T.map g.toRingHom :=
    Relative.EtaleNaturality.Construction.etale_homogenized_comparison_tangent_eq (σ := σ) f g hf hg J n hH
  have hcoord : ∀ j : σ,
      g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) -
        f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) ∈ L := by
    intro j
    by_cases hij : i = j
    · subst j
      rw [heq, ← map_sub]
      change g _ ∈ T.map f.toRingHom
      rw [hT]
      exact Ideal.mem_map_of_mem g.toRingHom (T.sub_mem hi hz)
    · rw [hcomp j hij, sub_self]
      exact L.zero_mem
  have hbase : ∀ p : MvPolynomial σ k,
      g (algebraMap (MvPolynomial σ k) R p) - f (algebraMap (MvPolynomial σ k) R p) ∈ L := by
    let Q := Ideal.Quotient.mkₐ k L
    let α := IsScalarTower.toAlgHom k (MvPolynomial σ k) R
    have hq : (Q.comp g).comp α = (Q.comp f).comp α := by
      apply MvPolynomial.algHom_ext
      intro j
      exact Ideal.Quotient.eq.mpr (hcoord j)
    exact fun p => Ideal.Quotient.eq.mp (AlgHom.congr_fun hq p)
  let q := RingHom.ker v.toRingHom
  let : q.IsPrime := Ideal.comap_isPrime v.toRingHom ⊥
  have hq : ∀ x : R, g x - f x ∈ q := by
    intro x
    change v (g x - f x) = 0
    rw [map_sub, hv x, sub_self]
  obtain ⟨s, hs, hann⟩ := Blowups.Ideal.ImageCongruence.Construction.unramified_congruence_neighborhood_any_ideal
    (P := MvPolynomial σ k) f.toRingHom g.toRingHom L q hbase hq
  let U := Localization.Away s
  let η : S →ₐ[k] U := IsScalarTower.toAlgHom k S U
  have hunit : IsUnit (v s) := isUnit_iff_ne_zero.mpr hs
  let v' : U →ₐ[k] C := IsLocalization.Away.liftAlgHom s hunit
  have hηs : IsUnit (η s) := IsLocalization.Away.algebraMap_isUnit s
  have hT' : T.map (η.toRingHom.comp f.toRingHom) = T.map (η.toRingHom.comp g.toRingHom) := by
    rw [← Ideal.map_map, ← Ideal.map_map, hT]
  have hdiff : ∀ x : R,
      (η.toRingHom.comp g.toRingHom) x - (η.toRingHom.comp f.toRingHom) x ∈
        T.map (η.toRingHom.comp f.toRingHom) := by
    intro x
    have h := Ideal.mem_map_of_mem η.toRingHom (hann x)
    rw [map_mul] at h
    have h' := (Ideal.unit_mul_mem_iff_mem _ hηs).mp h
    change η (g x - f x) ∈ (T.map f.toRingHom).map η.toRingHom at h'
    rw [map_sub, Ideal.map_map] at h'
    exact h'
  refine ⟨U, inferInstance, inferInstance, η, v', ?_, ?_, hT', hdiff, ?_⟩
  · change (algebraMap S U).Etale
    exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway s)
  · intro x
    exact IsLocalization.Away.lift_eq s hunit x
  · intro I hI
    have h := Blowups.Ideal.ImageCongruence.Construction.ideal_images_eq_of_congruence (η.toRingHom.comp f.toRingHom)
      (η.toRingHom.comp g.toRingHom) T I hT' hdiff (Blowups.Ideal.ImageCongruence.Construction.relative_tangent_le_permissible_center k J I n hI)
    simpa only [Ideal.map_map] using h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TangentCongruentComparisonRefinement.Construction
