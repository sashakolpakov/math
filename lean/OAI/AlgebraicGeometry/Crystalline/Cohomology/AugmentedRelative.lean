import OAI.AlgebraicGeometry.Crystalline.Cohomology.AugmentationIdeal

/-! # Augmented Relative -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.AugmentedRelative.AugmentedRelativeQuotient

noncomputable section

/-!
# Coefficient quotients of relative augmented PD algebras

For an augmented algebra with PD ideal the inverse image of the base
ideal, compatibility with a coefficient quotient reduces to compatibility
on the base. The augmentation splitting separates a base-ideal term
from a product-ideal term, both of which have stable positive divided
powers. No flatness or characteristic hypothesis is used.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (ε : A →ₐ[R] R) (I : Ideal R) (δI : DividedPowers I)
  (J : Ideal A) (δJ : DividedPowers J) (hJ : J = I.comap ε.toRingHom)
  (hbase : DividedPowers.IsDPMorphism δI δJ (algebraMap R A))
  (L : Ideal R) (hL : DividedPowers.IsSubDPIdeal δI (L ⊓ I))

include hJ hbase hL in
/-- A coefficient quotient preserves the full relative PD structure. -/
theorem isSubDPIdeal :
    DividedPowers.IsSubDPIdeal δJ (L.map (algebraMap R A) ⊓ J) := by
  refine ⟨inf_le_right, ?_⟩
  intro n hn a ha
  refine ⟨?_, δJ.dpow_mem hn ha.2⟩
  have hcI : ε a ∈ I := by
    rw [hJ] at ha
    exact ha.2
  have hcL : ε a ∈ L := by
    have h := Base.IdealQuotient.BaseIdealQuotient.map_mem L ε.toLinearMap ha.1
    rw [Algebra.algebraMap_self, Ideal.map_id] at h
    exact h
  have hker : RingHom.ker ε.toRingHom ≤ J := by
    rw [hJ]
    intro b hb
    change ε b ∈ I
    rw [show ε b = 0 from hb]
    exact I.zero_mem
  let b := AugmentationIdeal.AugmentationIdealIntersection.projection R A ε a
  let c := algebraMap R A (ε a)
  have hbJ : b ∈ J := hker (AugmentationIdeal.AugmentationIdealIntersection.projection_mem R A ε a)
  have hcJ : c ∈ J := hbase.ideal_comp (Ideal.mem_map_of_mem _ hcI)
  have hab : a = b + c := (sub_add_cancel a c).symm
  have hbprod : b ∈ J * L.map (algebraMap R A) := by
    rw [mul_comm]
    exact (Ideal.mul_mono le_rfl hker) (AugmentationIdeal.AugmentationIdealIntersection.projection_mem_product R A ε L a ha.1)
  have hbpow (k : ℕ) (hk : k ≠ 0) : δJ.dpow k b ∈ L.map (algebraMap R A) :=
    Ideal.mul_le_right ((DividedPowers.SubDPIdeal.prod (hI := δJ)
      (L.map (algebraMap R A))).toIsSubDPIdeal.dpow_mem k hk hbprod)
  have hcpow (k : ℕ) (hk : k ≠ 0) : δJ.dpow k c ∈ L.map (algebraMap R A) := by
    have hc := Ideal.mem_map_of_mem (algebraMap R A) (hL.dpow_mem k hk ⟨hcL, hcI⟩).1
    have hd : algebraMap R A (δI.dpow k (ε a)) = δJ.dpow k c := hbase.map_dpow hcI
    exact hd ▸ hc
  rw [hab, δJ.dpow_add hbJ hcJ]
  apply Submodule.sum_mem
  intro ij hij
  by_cases hi : ij.1 = 0
  · have hj : ij.2 ≠ 0 := by
      intro hj
      have hs := Finset.mem_antidiagonal.mp hij
      rw [hi, hj, zero_add] at hs
      exact hn hs.symm
    exact Ideal.mul_mem_left _ _ (hcpow ij.2 hj)
  · exact Ideal.mul_mem_right _ _ (hbpow ij.1 hi)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.AugmentedRelative.AugmentedRelativeQuotient
