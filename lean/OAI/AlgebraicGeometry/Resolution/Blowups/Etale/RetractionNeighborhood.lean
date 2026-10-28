import OAI.AlgebraicGeometry.Resolution.Blowups.UnramifiedCongruenceNeighborhood
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Retraction Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RetractionNeighborhood.Construction

noncomputable section

/-! An actual principal neighborhood of a section of an unramified affine morphism. -/

variable {H A : Type*} [CommRing H] [CommRing A] [Algebra H A]
  [Algebra.EssFiniteType H A] [Algebra.FormallyUnramified H A]

/-- A retraction of an unramified algebra has an idempotent principal kernel. -/
theorem unramified_retraction_kernel_idempotent (r : A →ₐ[H] H) :
    ∃ e : A, IsIdempotentElem e ∧ RingHom.ker r = Ideal.span {e} := by
  let g : A →ₐ[H] A := (Algebra.ofId H A).comp r
  obtain ⟨e, he, hspan⟩ := UnramifiedCongruenceNeighborhood.Construction.unramified_differenceIdeal_idempotent (AlgHom.id H A) g
  refine ⟨e, he, ?_⟩
  rw [← hspan]
  apply le_antisymm
  · intro a ha
    have hmem : g a - a ∈ Ideal.span (Set.range (fun x : A => g x - x)) :=
      Ideal.subset_span (Set.mem_range_self a)
    have hra : r a = 0 := ha
    have heq : g a - a = -a := by simp only [g, AlgHom.comp_apply, hra, map_zero, zero_sub]
    rw [heq] at hmem
    exact neg_mem_iff.mp hmem
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change r (g a - a) = 0
    simp [g]

/-- A single principal neighborhood contains the whole section and removes
the complementary unramified branches. -/
theorem unramified_retraction_annihilator (r : A →ₐ[H] H) :
    ∃ s : A, r s = 1 ∧ ∀ a : A, s * (algebraMap H A (r a) - a) = 0 := by
  obtain ⟨e, he, hker⟩ := unramified_retraction_kernel_idempotent r
  have hre : r e = 0 := by
    change e ∈ RingHom.ker r
    rw [hker]
    exact Ideal.mem_span_singleton_self e
  refine ⟨1 - e, by rw [map_sub, map_one, hre, sub_zero], ?_⟩
  intro a
  have ha : algebraMap H A (r a) - a ∈ Ideal.span {e} := by
    rw [← hker]
    change r (algebraMap H A (r a) - a) = 0
    simp
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
  rw [hb, ← mul_assoc, he.one_sub_mul_self, zero_mul]

/-- After restricting to that principal neighborhood, the section is an
actual algebra isomorphism with the base. -/
theorem exists_unramified_retraction_localization (r : A →ₐ[H] H) :
    ∃ (s : A) (e : Localization.Away s ≃ₐ[H] H),
      r s = 1 ∧ e.toRingHom.comp (algebraMap A (Localization.Away s)) = r.toRingHom := by
  obtain ⟨s, hs, hann⟩ := unramified_retraction_annihilator r
  let B := Localization.Away s
  have hu : IsUnit (r s) := hs ▸ isUnit_one
  let l : B →ₐ[H] H := IsLocalization.Away.liftAlgHom (f := r) s hu
  have hl (a : A) : l (algebraMap A B a) = r a := IsLocalization.Away.lift_eq s hu a
  let c : H →ₐ[H] B := Algebra.ofId H B
  have hlc : l.comp c = AlgHom.id H H := by
    ext
  have hcl : c.comp l = AlgHom.id H B := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    apply RingHom.ext
    intro a
    change algebraMap H B (l (algebraMap A B a)) = algebraMap A B a
    rw [hl, IsScalarTower.algebraMap_apply H A B]
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (IsLocalization.Away.algebraMap_isUnit s).mul_left_cancel
    rw [mul_zero, ← map_mul, hann, map_zero]
  refine ⟨s, AlgEquiv.ofAlgHom l c hlc hcl, hs, ?_⟩
  apply RingHom.ext
  exact hl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RetractionNeighborhood.Construction
