import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.TransverseRegularity
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Flat Principal Colon -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.FlatPrincipalColon.Construction

noncomputable section

/-! Principal ideal quotients commute with arbitrary flat scalar extension. -/

open TensorProduct

universe u

theorem flat_map_colon_principal {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (J : Ideal R) (c : R) :
    (J.colon (Ideal.span {c} : Set R)).map (algebraMap R S) =
      (J.map (algebraMap R S)).colon (Ideal.span {algebraMap R S c} : Set S) := by
  apply le_antisymm (Boundary.TransverseRegularity.Construction.map_colon_principal_le J c (algebraMap R S))
  intro x hx
  let f : R →ₗ[R] R ⧸ J := LinearMap.toSpanSingleton R (R ⧸ J) (Ideal.Quotient.mk J c)
  have hxker : x ⊗ₜ[R] (1 : R) ∈ LinearMap.ker (AlgebraTensorModule.lTensor S S f) := by
    rw [LinearMap.mem_ker]
    change x ⊗ₜ[R] f 1 = 0
    have hf : f 1 = Ideal.Quotient.mk J c := by
      change (1 : R) • Ideal.Quotient.mk J c = _
      rw [one_smul]
    rw [hf]
    apply (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S J).symm.injective
    rw [map_zero, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
    rw [Algebra.smul_def]
    change Ideal.Quotient.mk (J.map (algebraMap R S)) (algebraMap R S c * x) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [mul_comm] using Ideal.mem_colon_span_singleton.mp hx
  rw [Module.Flat.ker_lTensor_eq S S f] at hxker
  obtain ⟨t, ht⟩ := hxker
  have hmem : ∀ t : S ⊗[R] LinearMap.ker f,
      TensorProduct.rid R S (AlgebraTensorModule.lTensor S S (LinearMap.ker f).subtype t) ∈
        (J.colon (Ideal.span {c} : Set R)).map (algebraMap R S) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul s r =>
        have hr : r.val ∈ J.colon (Ideal.span {c} : Set R) := by
          apply Ideal.mem_colon_span_singleton.mpr
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          have h := r.property
          change f r.val = 0 at h
          change Ideal.Quotient.mk J (r.val * c) = 0 at h
          exact h
        simp only [AlgebraTensorModule.lTensor_tmul, Submodule.coe_subtype, TensorProduct.rid_tmul]
        rw [Algebra.smul_def]
        change algebraMap R S r.val * s ∈ _
        exact Ideal.mul_mem_right s _ (Ideal.mem_map_of_mem (algebraMap R S) hr)
    | add t v ht hv =>
        rw [map_add, map_add]
        exact Ideal.add_mem _ ht hv
  have h := hmem t
  rw [ht] at h
  simpa only [TensorProduct.rid_tmul, one_smul] using h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.FlatPrincipalColon.Construction
