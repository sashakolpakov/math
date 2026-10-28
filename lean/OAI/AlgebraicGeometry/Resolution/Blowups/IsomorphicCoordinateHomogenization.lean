import OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizedCoordinateComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialEquiv
import OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalOpenIdealComparison

/-! # Isomorphic Coordinate Homogenization -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicCoordinateHomogenization.Construction

noncomputable section

/-! Homogenization comparison for two isomorphic ambient charts with one changed coordinate. -/

variable {σ k R S T : Type*} [CommRing k] [CommRing R] [CommRing S] [CommRing T]
  [Algebra k R] [Algebra k S] [Algebra k T] [Algebra ℚ R] [Algebra ℚ S] [Algebra ℚ T]
  [Algebra (MvPolynomial σ k) R] [Algebra (MvPolynomial σ k) S]
  [IsScalarTower k (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) S]
  [Algebra.EssFiniteType (MvPolynomial σ k) R]
  [Algebra.EssFiniteType (MvPolynomial σ k) S]
  [Algebra.FormallyUnramified (MvPolynomial σ k) R]
  [Algebra.FormallyUnramified (MvPolynomial σ k) S] [DecidableEq σ]

/-- If the two charts share their complementary coordinates, their changed
hypersurface coordinates lie in the tangent ideal, and their comparison maps
have a common point, their homogenized ideals agree on a constructed principal open. -/
theorem isomorphic_coordinate_homogenization_neighborhood
    (e : R ≃ₐ[k] S) (D : Derivation k R R) (E : Derivation k S S)
    (f g : R →ₐ[k] T) (J : Ideal R) (i : σ) (n : ℕ)
    (hD : ∀ a : σ, D (algebraMap (MvPolynomial σ k) R (MvPolynomial.X a)) =
      if i = a then 1 else 0)
    (hE : ∀ a : σ, E (algebraMap (MvPolynomial σ k) S (MvPolynomial.X a)) =
      if i = a then 1 else 0)
    (hcommon : ∀ a : σ, i ≠ a →
      e.symm (algebraMap (MvPolynomial σ k) S (MvPolynomial.X a)) =
        algebraMap (MvPolynomial σ k) R (MvPolynomial.X a))
    (hcoords : ∀ a : σ, f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X a)) =
      g (e.symm (algebraMap (MvPolynomial σ k) S (MvPolynomial.X a))))
    (hz : algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) ∈
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hw : e.symm (algebraMap (MvPolynomial σ k) S (MvPolynomial.X i)) ∈
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (q : Ideal T) [q.IsPrime] (hq : ∀ x : R, g x - f x ∈ q) :
    ∃ s : T, s ∉ q ∧
      ((Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom).map
          (algebraMap T (Localization.Away s)) =
        ((Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map g.toRingHom).map
          (algebraMap T (Localization.Away s)) := by
  let z := algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)
  let w := e.symm (algebraMap (MvPolynomial σ k) S (MvPolynomial.X i))
  let F : S →ₐ[k] T := f.comp e.symm.toAlgHom
  let G : S →ₐ[k] T := g.comp e.symm.toAlgHom
  let JS := J.map e.toRingHom
  have hzw : f z = g w := hcoords i
  have hshiftD : ∀ a : σ,
      f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X a)) =
      g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X a)) +
        if i = a then g (w - z) else 0 := by
    intro a
    by_cases hia : i = a
    · subst a
      rw [ite_eq_left rfl]
      change f z = g z + g (w - z)
      rw [hzw, map_sub]
      ring
    · rw [ite_eq_right hia, add_zero, hcoords a, hcommon a hia]
  have hshiftE : ∀ a : σ,
      G (algebraMap (MvPolynomial σ k) S (MvPolynomial.X a)) =
      F (algebraMap (MvPolynomial σ k) S (MvPolynomial.X a)) +
        if i = a then f (z - w) else 0 := by
    intro a
    by_cases hia : i = a
    · subst a
      rw [ite_eq_left rfl]
      change g w = f w + f (z - w)
      rw [← hzw, map_sub]
      ring
    · rw [ite_eq_right hia, add_zero]
      change g (e.symm (algebraMap (MvPolynomial σ k) S (MvPolynomial.X a))) =
        f (e.symm (algebraMap (MvPolynomial σ k) S (MvPolynomial.X a)))
      rw [hcommon a hia, hcoords a, hcommon a hia]
  have hqrev : ∀ x : R, f x - g x ∈ q := by
    intro x
    simpa only [neg_sub] using q.neg_mem (hq x)
  have hqS : ∀ x : S, G x - F x ∈ q := fun x => hq (e.symm x)
  have htq : g (w - z) ∈ q := by
    have h := hqrev z
    rw [hzw, ← map_sub] at h
    exact h
  have huq : f (z - w) ∈ q := by
    have h := hq w
    rw [← hzw, ← map_sub] at h
    exact h
  have ht : g (w - z) ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map g.toRingHom :=
    Ideal.mem_map_of_mem g.toRingHom ((Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).sub_mem hw hz)
  have hδ : e (z - w) ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k JS n := by
    rw [← Relative.DifferentialEquiv.Construction.iteratedRelativeDifferentialIdeal_map_equiv]
    exact Ideal.mem_map_of_mem e.toRingHom
      ((Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).sub_mem hz hw)
  have hu : f (z - w) ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k JS n).map F.toRingHom := by
    have h := Ideal.mem_map_of_mem F.toRingHom hδ
    change f (e.symm (e (z - w))) ∈ _ at h
    rw [e.symm_apply_apply] at h
    exact h
  have hfg := HomogenizedCoordinateComparison.Construction.etale_coordinate_shift_homogenized_neighborhood D g f J i (g (w - z)) n
    hD hshiftD q htq hqrev ht
  have hgf := HomogenizedCoordinateComparison.Construction.etale_coordinate_shift_homogenized_neighborhood E F G JS i (f (z - w)) n
    hE hshiftE q huq hqS hu
  have hF : F.toRingHom.comp e.toRingHom = f.toRingHom := by
    ext x
    change f (e.symm (e x)) = f x
    rw [e.symm_apply_apply]
  have hG : G.toRingHom.comp e.toRingHom = g.toRingHom := by
    ext x
    change g (e.symm (e x)) = g x
    rw [e.symm_apply_apply]
  have hHF : (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k JS n).map F.toRingHom =
      (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom := by
    rw [← Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal_map_equiv e J n, Ideal.map_map, hF]
  have hHG : (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k JS n).map G.toRingHom =
      (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map g.toRingHom := by
    rw [← Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal_map_equiv e J n, Ideal.map_map, hG]
  rw [hHF, hHG] at hgf
  exact PrincipalOpenIdealComparison.Construction.exists_common_principal_ideal_equality
    ((Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom)
    ((Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map g.toRingHom) q hfg hgf

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IsomorphicCoordinateHomogenization.Construction
