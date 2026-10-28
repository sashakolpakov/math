import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ShearedCoordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.NonzeroPartialTangentComparison

/-! # Tangent Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.TangentComparison.Construction

noncomputable section

/-! Boundary-preserving transverse comparisons retain tangent congruence. -/

universe u

variable {σ k R C : Type u} [Field k] [CommRing R] [Field C]
  [Algebra k R] [Algebra k C] [Algebra ℚ R]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
  [IsScalarTower k (MvPolynomial σ k) R] [Fintype σ] [DecidableEq σ]

/-- Any tangent-ideal equation transverse to the retained boundary can be
compared with a transverse coordinate hypersurface. The common étale chart,
point, hypersurface alignment, boundary equations, homogenized-ideal equality,
and compatibility with every permissible embedded center are all constructed. -/
theorem exists_boundary_transverse_tangent_comparison
    (J : Ideal R) (B : Finset σ) (i : σ) (hiB : i ∉ B) (z : R) (n : ℕ) (r : R →ₐ[k] C)
    (htrans : ∃ j : σ, j ∉ B ∧ r (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) j z) ≠ 0)
    (hi : algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) ∈
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hpoint : r (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)) = r z) :
    ∃ (U : Type u) (_ : CommRing U) (_ : Algebra k U),
      ∃ f g : R →ₐ[k] U, ∃ v : U →ₐ[k] C,
        f.toRingHom.Etale ∧ g.toRingHom.Etale ∧
        f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)) = g z ∧
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
  by_cases hpi : r (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i z) ≠ 0
  · obtain ⟨U, instU, instkU, f, g, v, hf, hg, heq, hcomp, hH, hvf, hvg, hT, hdiff, hcenters⟩ :=
      NonzeroPartialTangentComparison.Construction.exists_nonzero_partial_tangent_comparison J i z n r hpi hi hz hpoint
    refine ⟨U, instU, instkU, f, g, v, hf, hg, heq, ?_, hH, hvf, hvg, hT, hdiff, hcenters⟩
    intro b hb
    exact hcomp b (fun he => hiB (he.symm ▸ hb))
  · have hzero : r (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i z) = 0 := not_ne_iff.mp hpi
    obtain ⟨j, hjB, hpj⟩ := htrans
    have hij : i ≠ j := by
      intro h
      subst j
      exact hpj hzero
    obtain ⟨S, instS, instkS, instPS, htor, hS, e, hcoords⟩ :=
      Blowups.Etale.ShearedCoordinates.Construction.exists_etale_sheared_coordinates (k := k) (R := R) i j hij
    let : CommRing S := instS
    let : Algebra k S := instkS
    let : Algebra (MvPolynomial σ k) S := instPS
    let : IsScalarTower k (MvPolynomial σ k) S := htor
    let : Algebra.Etale (MvPolynomial σ k) S := hS
    let : Algebra ℚ S := (e.toRingHom.comp (algebraMap ℚ R)).toAlgebra
    let J' := J.map e.toRingHom
    let r' := r.comp e.symm.toAlgHom
    have hfix : ∀ a : σ, a ≠ j → algebraMap (MvPolynomial σ k) S (MvPolynomial.X a) =
        e (algebraMap (MvPolynomial σ k) R (MvPolynomial.X a)) := by
      intro a haj
      rw [hcoords a, ite_eq_right haj]
    have hnewpartial : r' (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := S) i (e z)) ≠ 0 := by
      rw [Blowups.Etale.ShearPartial.Construction.etale_shear_partial_formula e i j hij hcoords z]
      change r (e.symm (e _)) ≠ 0
      rw [e.symm_apply_apply, map_add, hzero, zero_add]
      exact hpj
    have hi' : algebraMap (MvPolynomial σ k) S (MvPolynomial.X i) ∈
        Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J' n := by
      rw [hfix i hij, ← Relative.DifferentialEquiv.Construction.iteratedRelativeDifferentialIdeal_map_equiv]
      exact Ideal.mem_map_of_mem e.toRingHom hi
    have hz' : e z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J' n := by
      rw [← Relative.DifferentialEquiv.Construction.iteratedRelativeDifferentialIdeal_map_equiv]
      exact Ideal.mem_map_of_mem e.toRingHom hz
    have hp : r' (algebraMap (MvPolynomial σ k) S (MvPolynomial.X i)) = r' (e z) := by
      rw [hfix i hij]
      change r (e.symm (e _)) = r (e.symm (e z))
      rw [e.symm_apply_apply, e.symm_apply_apply]
      exact hpoint
    obtain ⟨U, instU, instkU, F, G, v, hF, hG, heq, hcomp, hH, hvF, hvG, hT, hdiff, hcenters⟩ :=
      NonzeroPartialTangentComparison.Construction.exists_nonzero_partial_tangent_comparison J' i (e z) n r'
        hnewpartial hi' hz' hp
    let f := F.comp e.toAlgHom
    let g := G.comp e.toAlgHom
    have hf : f.toRingHom = F.toRingHom.comp e.toRingHom := by
      ext x
      rfl
    have hg : g.toRingHom = G.toRingHom.comp e.toRingHom := by
      ext x
      rfl
    refine ⟨U, instU, instkU, f, g, v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hf]
      exact RingHom.Etale.stableUnderComposition e.toRingHom F.toRingHom
        (RingHom.Etale.of_bijective e.bijective) hF
    · rw [hg]
      exact RingHom.Etale.stableUnderComposition e.toRingHom G.toRingHom
        (RingHom.Etale.of_bijective e.bijective) hG
    · rw [hfix i hij] at heq
      exact heq
    · intro b hb
      have hib : i ≠ b := fun he => hiB (he.symm ▸ hb)
      have hbj : b ≠ j := fun he => hjB (he ▸ hb)
      have h := hcomp b hib
      rw [hfix b hbj] at h
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

    · rw [hf, hg, ← Ideal.map_map, ← Ideal.map_map, Relative.DifferentialEquiv.Construction.iteratedRelativeDifferentialIdeal_map_equiv]
      exact hT
    · intro x
      have h := hdiff (e x)
      rw [hf, ← Ideal.map_map, Relative.DifferentialEquiv.Construction.iteratedRelativeDifferentialIdeal_map_equiv]
      exact h
    · intro I hI
      have hI' : J' ≤ (I.map e.toRingHom) ^ (n + 1) := by
        rw [← Ideal.map_pow]
        exact Ideal.map_mono hI
      have h := hcenters (I.map e.toRingHom) hI'
      rw [Ideal.map_map, Ideal.map_map] at h
      rw [hf, hg]
      exact h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.TangentComparison.Construction
