import OAI.AlgebraicGeometry.Resolution.Blowups.EquationUnitTangentComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.HomogenizationBaseChange

/-! # Two Transverse Tangent Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TwoTransverseTangentComparison.Construction

noncomputable section

/-! Pointed tangent-congruent comparisons for independently chosen maximal-contact equations. -/

universe u

variable {σ k R C : Type u} [Field k] [CommRing R] [Field C]
  [Algebra k R] [Algebra k C] [Algebra ℚ R]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
  [IsScalarTower k (MvPolynomial σ k) R] [Fintype σ] [DecidableEq σ]

/-- Two independently selected transverse tangent equations have a
constructed pointed étale comparison identifying their hypersurfaces and
homogenized ideals, fixing the retained boundary and every permissible center. -/
theorem exists_two_transverse_equation_tangent_comparison
    (J : Ideal R) (B : Finset σ) (z t : R) (n : ℕ) (r : R →ₐ[k] C)
    (htransz : ∃ i : σ, i ∉ B ∧ r (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i z) ≠ 0)
    (htranst : ∃ j : σ, j ∉ B ∧ r (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) j t) ≠ 0)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) (hpoint : r z = r t) :
    ∃ (U : Type u) (_ : CommRing U) (_ : Algebra k U),
      ∃ f g : R →ₐ[k] U, ∃ v : U →ₐ[k] C,
        f.toRingHom.Etale ∧ g.toRingHom.Etale ∧ f z = g t ∧
        (∀ b ∈ B,
          f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X b)) =
            g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X b))) ∧
        (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom =
          (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map g.toRingHom ∧
        (∀ x : R, v (f x) = r x) ∧ (∀ x : R, v (g x) = r x) ∧
        (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom =
          (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map g.toRingHom ∧
        (∀ x : R, g x - f x ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom) ∧
        ∀ I : Ideal R, J ≤ I ^ (n + 1) → I.map f.toRingHom = I.map g.toRingHom := by
  obtain ⟨i, hiB, hiz⟩ := htransz
  let d := Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i z
  let A := Localization.Away d
  let : Algebra.Etale R A := Algebra.Etale.of_isLocalizationAway d
  let : Algebra.Etale (MvPolynomial σ k) A := Algebra.Etale.comp (MvPolynomial σ k) R A
  let a : R →ₐ[k] A := IsScalarTower.toAlgHom k R A
  let J' := J.map a.toRingHom
  have hunit : IsUnit (r d) := isUnit_iff_ne_zero.mpr hiz
  let r' : A →ₐ[k] C := IsLocalization.Away.liftAlgHom d hunit
  have hra : ∀ x : R, r' (a x) = r x := fun x => IsLocalization.Away.lift_eq d hunit x
  have hco : ∀ j : σ, algebraMap (MvPolynomial σ k) A (MvPolynomial.X j) =
      a (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) :=
    fun j => IsScalarTower.algebraMap_apply (MvPolynomial σ k) R A (MvPolynomial.X j)
  have hpart : IsUnit (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := A) i (a z)) := by
    change IsUnit (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := A) i (algebraMap R A z))
    rw [Blowups.Etale.RelativePartialBaseChange.Construction.etaleRelativePartial_baseChange (S := R) (T := A)]
    exact IsLocalization.Away.algebraMap_isUnit d
  have httrans : ∃ j : σ, j ∉ B ∧ r' (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := A) j (a t)) ≠ 0 := by
    obtain ⟨j, hjB, hjt⟩ := htranst
    refine ⟨j, hjB, ?_⟩
    change r' (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := A) j (algebraMap R A t)) ≠ 0
    rw [Blowups.Etale.RelativePartialBaseChange.Construction.etaleRelativePartial_baseChange (S := R) (T := A)]
    exact (hra _).trans_ne hjt
  have hδ : (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map a.toRingHom =
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J' n :=
    Relative.DifferentialBaseChange.Construction.etale_iteratedRelativeDifferentialIdeal_baseChange (σ := σ) J n
  have hz' : a z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J' n := by
    rw [← hδ]
    exact Ideal.mem_map_of_mem a.toRingHom hz
  have ht' : a t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J' n := by
    rw [← hδ]
    exact Ideal.mem_map_of_mem a.toRingHom ht
  have hp : r' (a z) = r' (a t) := by rw [hra, hra, hpoint]
  obtain ⟨U, instU, instkU, F, G, v, hF, hG, heq, hB, hH, hvF, hvG, hT, hdiff, hcenters⟩ :=
    EquationUnitTangentComparison.Construction.exists_two_equation_tangent_comparison_of_unit_partial J' B i hiB (a z) (a t) n r'
      hpart httrans hz' ht' hp
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
  refine ⟨U, instU, instkU, f, g, v, ?_, ?_, heq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf]
    exact RingHom.Etale.stableUnderComposition a.toRingHom F.toRingHom ha hF
  · rw [hg]
    exact RingHom.Etale.stableUnderComposition a.toRingHom G.toRingHom ha hG
  · intro j hj
    have h := hB j hj
    rw [hco] at h
    exact h
  · rw [hf, hg, ← Ideal.map_map, ← Ideal.map_map, hHbase]
    exact hH
  · intro x
    exact (hvF (a x)).trans (hra x)
  · intro x
    exact (hvG (a x)).trans (hra x)
  · rw [hf, hg, ← Ideal.map_map, ← Ideal.map_map, hδ]
    exact hT
  · intro x
    have h := hdiff (a x)
    rw [hf, ← Ideal.map_map, hδ]
    exact h
  · intro I hI
    have hI' : J' ≤ (I.map a.toRingHom) ^ (n + 1) := by
      rw [← Ideal.map_pow]
      exact Ideal.map_mono hI
    have h := hcenters (I.map a.toRingHom) hI'
    rw [Ideal.map_map, Ideal.map_map] at h
    rw [hf, hg]
    exact h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TwoTransverseTangentComparison.Construction
