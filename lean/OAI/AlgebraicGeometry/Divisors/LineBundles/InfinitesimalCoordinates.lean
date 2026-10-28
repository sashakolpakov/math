import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Infinitesimal Coordinates -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.InfinitesimalCoordinates.BundleCycles

noncomputable section

/-! # LineBundleCycles: infinitesimal lifts detect every power of the section ideal -/

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

theorem quotientPowerFactor_ker_pow (I : Ideal R) (n : ℕ) (hn : n ≠ 0) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self (I := I) hn)) ^ n = ⊥ := by
  have hk : RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self (I := I) hn)) =
      I.map (Ideal.Quotient.mk (I ^ n)) := by
    ext a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk I r = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_map_iff_of_surjective _
      Ideal.Quotient.mk_surjective]
    constructor
    · exact fun hr => ⟨r, hr, rfl⟩
    · rintro ⟨s, hs, hsr⟩
      have hsub := Ideal.pow_le_self (I := I) hn (Ideal.Quotient.eq.mp hsr)
      exact (I.sub_mem hs hsub) |> fun h => sub_sub_cancel s r ▸ h
  rw [hk, ← Ideal.map_pow, Ideal.map_quotient_self]

theorem formallySmooth_ker_power_comap [Algebra.FormallySmooth R S]
    (I : Ideal R) (q : S →ₐ[R] R ⧸ I) (n : ℕ) :
    (RingHom.ker q ^ n).comap (algebraMap R S) = I ^ n := by
  by_cases hn : n = 0
  · subst n
    simp
  let g : R ⧸ I ^ n →ₐ[R] R ⧸ I := Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn)
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨Ideal.Quotient.mk (I ^ n) r, rfl⟩
  have hgn : RingHom.ker g ^ n = ⊥ := quotientPowerFactor_ker_pow I n hn
  let l := Algebra.FormallySmooth.liftOfSurjective q g hg ⟨n, hgn⟩
  have hl : RingHom.ker q ≤ (RingHom.ker g).comap l := by
    intro s hs
    exact (Algebra.FormallySmooth.liftOfSurjective_apply q g hg ⟨n, hgn⟩ s).trans hs
  apply le_antisymm
  · intro r hr
    have h : l (algebraMap R S r) ∈ RingHom.ker g ^ n :=
      (Ideal.pow_right_mono hl n).trans (Ideal.le_comap_pow _ _) hr
    rw [hgn, Ideal.mem_bot, l.commutes] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  · have hI : I ≤ (RingHom.ker q).comap (algebraMap R S) := by
      intro r hr
      exact (q.commutes r).trans (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
    exact (Ideal.pow_right_mono hI n).trans (Ideal.le_comap_pow _ _)

theorem formallySmooth_ker_power_comap_of_surjective [Algebra.FormallySmooth R S]
    {C : Type} [CommRing C] [Algebra R C] (q : S →ₐ[R] C)
    (hC : Function.Surjective (algebraMap R C)) (n : ℕ) :
    (RingHom.ker q ^ n).comap (algebraMap R S) = RingHom.ker (algebraMap R C) ^ n := by
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R C) hC
  let q' := e.symm.toAlgHom.comp q
  have hk : RingHom.ker q'.toRingHom = RingHom.ker q.toRingHom :=
    RingHom.ker_comp_of_injective q.toRingHom e.symm.injective
  have h := formallySmooth_ker_power_comap (RingHom.ker (algebraMap R C)) q' n
  change (RingHom.ker q'.toRingHom ^ n).comap (algebraMap R S) = _ at h
  rw [hk] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.InfinitesimalCoordinates.BundleCycles
