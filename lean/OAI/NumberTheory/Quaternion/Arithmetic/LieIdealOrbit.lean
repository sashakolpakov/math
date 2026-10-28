import OAI.NumberTheory.Quaternion.Arithmetic.FiniteLieIdeals

/-! # Lie Ideal Orbit -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LieIdealOrbit

noncomputable section

/-! A Lie-ideal orbit fiber under an automorphism is described by a fixed
dimension and linear inclusion. This reduces its algebraic closedness to
the adjoint subspace conditions. -/

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]

omit [FiniteDimensional k L] in
theorem finrank_lieIdeal_image (e : L ≃ₗ⁅k⁆ L) (I : LieIdeal k L) :
    Module.finrank k (I.map e.toLieHom) = Module.finrank k I := by
  change Module.finrank k (I.map e.toLieHom).toSubmodule = Module.finrank k I.toSubmodule
  rw [LieIdeal.coe_map_of_surjective e.surjective]
  exact e.toLinearEquiv.finrank_map_eq I.toSubmodule

theorem lieIdeal_image_eq_iff (e : L ≃ₗ⁅k⁆ L) (I J : LieIdeal k L) :
    I.map e.toLieHom = J ↔ Module.finrank k I = Module.finrank k J ∧
      ∀ x ∈ I, e x ∈ J := by
  constructor
  · intro h
    constructor
    · rw [← h]
      exact (finrank_lieIdeal_image e I).symm
    · intro x hx
      rw [← h]
      exact LieIdeal.mem_map hx
  · rintro ⟨hd, hmem⟩
    have hle : I.map e.toLieHom ≤ J := LieIdeal.map_le_iff_le_comap.mpr hmem
    apply LieSubmodule.toSubmodule_injective
    apply Submodule.eq_of_le_of_finrank_eq hle
    exact (finrank_lieIdeal_image e I).trans hd

end

end OAI.NumberTheory.Quaternion.Arithmetic.LieIdealOrbit
