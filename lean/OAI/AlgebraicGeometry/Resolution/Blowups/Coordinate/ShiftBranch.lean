import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.HomogenizationComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.UnramifiedCongruenceNeighborhood

/-! # Shift Branch -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.ShiftBranch.Construction

noncomputable section

/-! Constructing the open branch needed for homogenization comparison. -/

variable {σ k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]
  [Algebra (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) R]
  [DecidableEq σ]

theorem coordinate_shift_base_congruence (f g : R →ₐ[k] S) (i : σ) (t : S)
    (hcoords : ∀ j : σ, g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) =
      f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) +
        if i = j then t else 0) (p : MvPolynomial σ k) :
    g (algebraMap (MvPolynomial σ k) R p) -
      f (algebraMap (MvPolynomial σ k) R p) ∈ Ideal.span {t} := by
  let Q := Ideal.Quotient.mkₐ k (Ideal.span {t})
  let α := IsScalarTower.toAlgHom k (MvPolynomial σ k) R
  have ht : Q t = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton_self t)
  have he : (Q.comp g).comp α = (Q.comp f).comp α := by
    apply MvPolynomial.algHom_ext
    intro j
    change Q (g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j))) =
      Q (f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)))
    rw [hcoords j, map_add]
    split_ifs <;> simp [ht]
  exact Ideal.Quotient.eq.mp (AlgHom.congr_fun he p)

variable [Algebra ℚ R] [Algebra ℚ S]
  [Algebra.EssFiniteType (MvPolynomial σ k) R]
  [Algebra.FormallyUnramified (MvPolynomial σ k) R]

/-- At a common point of two shifted coordinate charts, construct a principal
open on which the full algebraic homogenization comparison holds. -/
theorem etale_coordinate_shift_homogenization_neighborhood (D : Derivation k R R)
    (f g : R →ₐ[k] S) (J : Ideal R) (i : σ) (t : S) (n : ℕ)
    (hD : ∀ j : σ, D (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) =
      if i = j then 1 else 0)
    (hcoords : ∀ j : σ, g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) =
      f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) +
        if i = j then t else 0)
    (q : Ideal S) [q.IsPrime] (htq : t ∈ q)
    (hq : ∀ x : R, g x - f x ∈ q)
    (hT : t ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom) :
    ∃ s : S, s ∉ q ∧
      (J.map g.toRingHom).map (algebraMap S (Localization.Away s)) ≤
        ((Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom).map
          (algebraMap S (Localization.Away s)) := by
  obtain ⟨s, hs, hbranch⟩ := UnramifiedCongruenceNeighborhood.Construction.unramified_congruence_principal_open
    (P := MvPolynomial σ k) f.toRingHom g.toRingHom (Ideal.span {t}) q
    ((Ideal.span_singleton_le_iff_mem q).mpr htq)
    (coordinate_shift_base_congruence f g i t hcoords) hq
  let α := IsScalarTower.toAlgHom k S (Localization.Away s)
  let f' := α.comp f
  let g' := α.comp g
  have hcoords' : ∀ j : σ,
      g' (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) =
      f' (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) +
        if i = j then α t else 0 := by
    intro j
    change α (g _) = α (f _) + _
    rw [hcoords j, map_add]
    split_ifs <;> simp
  have hred' : ∀ x : R, g' x - f' x ∈ Ideal.span {α t} := by
    intro x
    have h := hbranch x
    rw [Ideal.map_span, Set.image_singleton] at h
    change α (g x - f x) ∈ Ideal.span {α t} at h
    rw [map_sub] at h
    exact h
  have hT' : α t ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f'.toRingHom := by
    change α t ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map
      (α.toRingHom.comp f.toRingHom)
    rw [← Ideal.map_map]
    exact Ideal.mem_map_of_mem α.toRingHom hT
  have hc := Etale.HomogenizationComparison.Construction.etale_coordinate_shift_ideal_le_homogenized D f' g' J i (α t) n
    hD hcoords' hred' hT'
  have hf' : f'.toRingHom = (algebraMap S (Localization.Away s)).comp f.toRingHom := by
    ext x
    rfl
  have hg' : g'.toRingHom = (algebraMap S (Localization.Away s)).comp g.toRingHom := by
    ext x
    rfl
  rw [hf', hg'] at hc
  refine ⟨s, hs, ?_⟩
  simpa only [Ideal.map_map] using hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.ShiftBranch.Construction
