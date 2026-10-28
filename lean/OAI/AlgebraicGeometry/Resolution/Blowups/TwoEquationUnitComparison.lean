import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateCopy
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TransverseDirection

/-! # Two Equation Unit Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TwoEquationUnitComparison.Construction

noncomputable section

/-! Compare two transverse tangent equations after making one a coordinate. -/

universe u

variable {σ k R C : Type u} [Field k] [CommRing R] [Field C]
  [Algebra k R] [Algebra k C] [Algebra ℚ R]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
  [IsScalarTower k (MvPolynomial σ k) R] [Fintype σ] [DecidableEq σ]

/-- Both hypersurfaces may be arbitrary transverse equations in the relative
tangent ideal. A unit partial of the first gives its coordinate presentation;
transversality of the second is transported using a boundary-annihilating
derivation. The resulting comparison preserves all permissible center ideals. -/
theorem exists_two_equation_comparison_of_unit_partial
    (J : Ideal R) (B : Finset σ) (i : σ) (hiB : i ∉ B) (z t : R) (n : ℕ)
    (r : R →ₐ[k] C) (hunit : IsUnit (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i z))
    (htrans : ∃ j : σ, j ∉ B ∧ r (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) j t) ≠ 0)
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
        ∀ I : Ideal R, J ≤ I ^ (n + 1) → I.map f.toRingHom = I.map g.toRingHom := by
  classical
  let τ := Option {j : σ // i ≠ j}
  let P := MvPolynomial τ k
  let β : P →ₐ[k] R := Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap i z
  obtain ⟨S, instS, instkS, instPS, htor, hS, e, he⟩ :=
    Blowups.Etale.CoordinateCopy.Construction.exists_isomorphic_etale_coordinate_copy β (Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_etale i z hunit)
  let : CommRing S := instS
  let : Algebra k S := instkS
  let : Algebra P S := instPS
  let : IsScalarTower k P S := htor
  let : Algebra.Etale P S := hS
  let : Algebra ℚ S := (e.toRingHom.comp (algebraMap ℚ R)).toAlgebra
  let B' : Finset τ := Finset.univ.filter (fun a => match a with
    | none => False
    | some j => j.val ∈ B)
  have hnone : (none : τ) ∉ B' := by simp [B']
  have hmem : ∀ j : {j : σ // i ≠ j}, (some j : τ) ∈ B' ↔ j.val ∈ B := by
    intro j
    simp [B']
  have hzcoord : algebraMap P S (MvPolynomial.X none) = e z := by
    rw [he]
    exact congrArg e (Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_none i z)
  have hcoords : ∀ j : {j : σ // i ≠ j},
      algebraMap P S (MvPolynomial.X (some j)) =
        e (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val)) := by
    intro j
    rw [he]
    exact congrArg e (Blowups.Etale.CoordinateReplacement.Construction.replacementCoordinateMap_some i z j)
  let J' := J.map e.toRingHom
  let r' := r.comp e.symm.toAlgHom
  have htrans' : ∃ j : τ, j ∉ B' ∧ r' (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := S) j (e t)) ≠ 0 := by
    obtain ⟨j, hjB, hjt⟩ := htrans
    let D := Relative.DifferentialEquiv.Construction.transportRelativeDerivation e (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) j)
    apply Blowups.Etale.TransverseDirection.Construction.exists_transverse_partial_of_boundary_derivation B' D r' (e t)
    · intro a ha
      cases a with
      | none => exact (hnone ha).elim
      | some a =>
        have haB := (hmem a).mp ha
        have hja : j ≠ a.val := fun h => hjB (h.symm ▸ haB)
        rw [hcoords]
        change Relative.DifferentialEquiv.Construction.transportRelativeDerivation e _ (e _) = 0
        rw [Relative.DifferentialEquiv.Construction.transportRelativeDerivation_map, Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X, ite_eq_right hja, map_zero]
    · change r (e.symm (D (e t))) ≠ 0
      rw [show D (e t) = e (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) j t) from
        Relative.DifferentialEquiv.Construction.transportRelativeDerivation_map e _ t, e.symm_apply_apply]
      exact hjt
  have hz' : algebraMap P S (MvPolynomial.X none) ∈
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J' n := by
    rw [hzcoord, ← Relative.DifferentialEquiv.Construction.iteratedRelativeDifferentialIdeal_map_equiv]
    exact Ideal.mem_map_of_mem e.toRingHom hz
  have ht' : e t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J' n := by
    rw [← Relative.DifferentialEquiv.Construction.iteratedRelativeDifferentialIdeal_map_equiv]
    exact Ideal.mem_map_of_mem e.toRingHom ht
  have hp : r' (algebraMap P S (MvPolynomial.X none)) = r' (e t) := by
    rw [hzcoord]
    change r (e.symm (e z)) = r (e.symm (e t))
    rw [e.symm_apply_apply, e.symm_apply_apply]
    exact hpoint
  obtain ⟨U, instU, instkU, F, G, v, hF, hG, heq, hB, hH, hvF, hvG, hcenters⟩ :=
    Boundary.CenterComparison.Construction.exists_boundary_transverse_center_comparison J' B' none hnone (e t) n r'
      htrans' hz' ht' hp
  let f := F.comp e.toAlgHom
  let g := G.comp e.toAlgHom
  have hf : f.toRingHom = F.toRingHom.comp e.toRingHom := by
    ext x
    rfl
  have hg : g.toRingHom = G.toRingHom.comp e.toRingHom := by
    ext x
    rfl
  refine ⟨U, instU, instkU, f, g, v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf]
    exact RingHom.Etale.stableUnderComposition e.toRingHom F.toRingHom
      (RingHom.Etale.of_bijective e.bijective) hF
  · rw [hg]
    exact RingHom.Etale.stableUnderComposition e.toRingHom G.toRingHom
      (RingHom.Etale.of_bijective e.bijective) hG
  · rw [hzcoord] at heq
    exact heq
  · intro b hb
    have hib : i ≠ b := fun h => hiB (h.symm ▸ hb)
    have h := hB (some ⟨b, hib⟩) ((hmem ⟨b, hib⟩).mpr hb)
    rw [hcoords] at h
    exact h
  · rw [hf, hg, ← Ideal.map_map, ← Ideal.map_map, Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal_map_equiv]
    exact hH
  · intro x
    have h := hvF (e x)
    change v (f x) = r (e.symm (e x)) at h
    rwa [e.symm_apply_apply] at h
  · intro x
    have h := hvG (e x)
    change v (g x) = r (e.symm (e x)) at h
    rwa [e.symm_apply_apply] at h
  · intro I hI
    have hI' : J' ≤ (I.map e.toRingHom) ^ (n + 1) := by
      rw [← Ideal.map_pow]
      exact Ideal.map_mono hI
    have h := hcenters (I.map e.toRingHom) hI'
    rw [Ideal.map_map, Ideal.map_map] at h
    rw [hf, hg]
    exact h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TwoEquationUnitComparison.Construction
