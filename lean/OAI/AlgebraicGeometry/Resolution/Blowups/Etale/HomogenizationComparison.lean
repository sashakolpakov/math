import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TaylorShift
import OAI.AlgebraicGeometry.Resolution.Blowups.TaylorHomogenization

/-! # Homogenization Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.HomogenizationComparison.Construction

noncomputable section

/-! Algebraic homogenization comparison across one changed étale coordinate. -/

variable {σ k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra ℚ R] [Algebra ℚ S]
  [Algebra (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) R]
  [Algebra.FormallyUnramified (MvPolynomial σ k) R] [DecidableEq σ]

/-- On a branch where the two maps agree modulo their coordinate displacement,
a displacement in the tangent ideal sends the original ideal into its
homogenization. The target displacement need not be nilpotent. -/
theorem etale_coordinate_shift_ideal_le_homogenized (D : Derivation k R R)
    (f g : R →ₐ[k] S) (J : Ideal R) (i : σ) (t : S) (n : ℕ)
    (hD : ∀ j : σ, D (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) =
      if i = j then 1 else 0)
    (hcoords : ∀ j : σ, g (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) =
      f (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) +
        if i = j then t else 0)
    (hred : ∀ x : R, g x - f x ∈ Ideal.span {t})
    (hT : t ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom) :
    J.map g.toRingHom ≤ (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom := by
  let I : Ideal S := Ideal.span {t ^ (n + 1)}
  let q : S →ₐ[k] S ⧸ I := Ideal.Quotient.mkₐ k I
  let fbar := q.comp f
  let gbar := q.comp g
  have hnil : (q t) ^ (n + 1) = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hcoordsbar : ∀ j : σ,
      gbar (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) =
      fbar (algebraMap (MvPolynomial σ k) R (MvPolynomial.X j)) +
        if i = j then q t else 0 := by
    intro j
    change q (g _) = q (f _) + _
    rw [hcoords j, map_add]
    split_ifs <;> simp
  have hredbar : ∀ x : R, gbar x - fbar x ∈ Ideal.span {q t} := by
    intro x
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (hred x)
    apply Ideal.mem_span_singleton.mpr
    refine ⟨q a, ?_⟩
    change q (g x) - q (f x) = q t * q a
    rw [← map_sub, ha, map_mul]
  have he := TaylorShift.Construction.etale_coordinate_shift_eq_taylor D fbar gbar i (q t) n hnil
    hD hcoordsbar hredbar
  have hTbar : q t ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map fbar.toRingHom := by
    change q t ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map
      (q.toRingHom.comp f.toRingHom)
    rw [← Ideal.map_map]
    exact Ideal.mem_map_of_mem q.toRingHom hT
  have hbar := TaylorHomogenization.Construction.nilpotentTaylorMap_ideal_le_homogenized D fbar J (q t) n hnil hTbar
  rw [← he] at hbar
  have hI : I ≤ (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom := by
    apply (Ideal.span_singleton_le_iff_mem
      ((Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom)).mpr
    have hp := Ideal.pow_mem_pow hT (n + 1)
    rw [← Ideal.map_pow] at hp
    exact Ideal.map_mono (Relative.DifferentialEquiv.Construction.tangentIdeal_power_le_relativeHomogenizedIdeal k J n) hp
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  have hxbar := hbar (Ideal.mem_map_of_mem gbar.toRingHom hx)
  change q (g x) ∈ (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map
    (q.toRingHom.comp f.toRingHom) at hxbar
  rw [← Ideal.map_map] at hxbar
  exact (Ideal.mem_quotient_iff_mem hI).mp hxbar

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.HomogenizationComparison.Construction
