import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IdealQuotient
import Mathlib.RingTheory.DividedPowers.SubDPIdeal

/-! # Augmentation Ideal -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.AugmentationIdeal.AugmentationIdealIntersection

noncomputable section

/-!
# Coefficient ideals and an augmentation kernel

In an augmented algebra, the intersection of an extended coefficient
ideal with the augmentation kernel is their product. Consequently any
PD structure on the augmentation kernel descends modulo arbitrary
coefficient ideals. No flatness or characteristic hypothesis is needed.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (ε : A →ₐ[R] R)

def projection : A →ₗ[R] A := LinearMap.id - (Algebra.linearMap R A).comp ε.toLinearMap

theorem projection_apply (a : A) : projection R A ε a = a - algebraMap R A (ε a) := rfl

theorem projection_mem (a : A) : projection R A ε a ∈ RingHom.ker ε.toRingHom := by
  change ε (a - algebraMap R A (ε a)) = 0
  rw [map_sub, ε.commutes, Algebra.algebraMap_self_apply, sub_self]

theorem projection_of_mem (a : A) (ha : a ∈ RingHom.ker ε.toRingHom) : projection R A ε a = a := by
  rw [projection_apply, show ε a = 0 from ha, map_zero, sub_zero]

variable (L : Ideal R)

theorem projection_mem_product (a : A) (ha : a ∈ L.map (algebraMap R A)) :
    projection R A ε a ∈ L.map (algebraMap R A) * RingHom.ker ε.toRingHom := by
  have ha' : a ∈ L • (⊤ : Submodule R A) := by
    rw [Ideal.smul_top_eq_map]
    exact ha
  clear ha
  induction ha' using Submodule.smul_induction_on' with
  | smul c hc b _ =>
    rw [map_smul, Algebra.smul_def]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hc) (projection_mem R A ε b)
  | add x _ y _ hx hy =>
    rw [map_add]
    exact Ideal.add_mem _ hx hy

theorem intersection_eq_product :
    L.map (algebraMap R A) ⊓ RingHom.ker ε.toRingHom =
      L.map (algebraMap R A) * RingHom.ker ε.toRingHom := by
  apply le_antisymm
  · intro a ha
    rw [← projection_of_mem R A ε a ha.2]
    exact projection_mem_product R A ε L a ha.1
  · exact le_inf Ideal.mul_le_left Ideal.mul_le_right

/-- Every coefficient quotient is compatible with divided powers on the augmentation kernel. -/
theorem isSubDPIdeal (δ : DividedPowers (RingHom.ker ε.toRingHom)) :
    DividedPowers.IsSubDPIdeal δ (L.map (algebraMap R A) ⊓ RingHom.ker ε.toRingHom) := by
  rw [intersection_eq_product, mul_comm]
  exact (DividedPowers.SubDPIdeal.prod (hI := δ) (L.map (algebraMap R A))).toIsSubDPIdeal

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.AugmentationIdeal.AugmentationIdealIntersection
