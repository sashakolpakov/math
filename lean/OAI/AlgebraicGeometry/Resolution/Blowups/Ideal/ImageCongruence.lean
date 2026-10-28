import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialEquiv
import OAI.AlgebraicGeometry.Resolution.Blowups.UnramifiedCongruenceNeighborhood

/-! # Image Congruence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.ImageCongruence.Construction

noncomputable section

/-! Congruent comparison maps preserve every ideal containing the tangent ideal. -/

section

variable {R S : Type*} [CommRing R] [CommRing S]

theorem ideal_images_eq_of_congruence (f g : R →+* S) (I L : Ideal R)
    (hI : I.map f = I.map g) (hdiff : ∀ x : R, g x - f x ∈ I.map f) (hIL : I ≤ L) :
    L.map f = L.map g := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change f x ∈ L.map g
    have hd := hdiff x
    rw [hI] at hd
    have hsub := (L.map g).sub_mem (Ideal.mem_map_of_mem g hx) (Ideal.map_mono hIL hd)
    simpa only [sub_sub_cancel] using hsub
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change g x ∈ L.map f
    have hadd := (L.map f).add_mem (Ideal.map_mono hIL (hdiff x)) (Ideal.mem_map_of_mem f hx)
    simpa only [sub_add_cancel] using hadd

variable {P : Type*} [CommRing P] [Algebra P R]
  [Algebra.EssFiniteType P R] [Algebra.FormallyUnramified P R]

/-- Congruence can be arranged near any common point, including points
outside the vanishing set of the comparison ideal. -/
theorem unramified_congruence_neighborhood_any_ideal (f g : R →+* S) (I q : Ideal S)
    [q.IsPrime]
    (hbase : ∀ p : P, g (algebraMap P R p) - f (algebraMap P R p) ∈ I)
    (hq : ∀ x : R, g x - f x ∈ q) :
    ∃ s : S, s ∉ q ∧ ∀ x : R, s * (g x - f x) ∈ I := by
  by_cases hIq : I ≤ q
  · exact UnramifiedCongruenceNeighborhood.Construction.unramified_congruence_neighborhood f g I q hIq hbase hq
  · obtain ⟨s, hsI, hsq⟩ := SetLike.not_le_iff_exists.mp hIq
    exact ⟨s, hsq, fun x => I.mul_mem_right (g x - f x) hsI⟩

end

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- Every permissible center contains the entire relative tangent ideal. -/
theorem relative_tangent_le_permissible_center (J I : Ideal R) (n : ℕ)
    (hJ : J ≤ I ^ (n + 1)) : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n ≤ I := by
  have h := (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k J n).trans
    (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow I J 1 n (by simpa only [Nat.add_comm 1 n] using hJ))
  simpa only [pow_one] using h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.ImageCongruence.Construction
