import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Product Coordinates -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.ProductCoordinates.Constructions

noncomputable section

/-! Explicit norm-preserving complex coordinates for finite product models,
including zero-dimensional factors. -/

def finiteProductCoordinates (d c : ℕ) :
    ((Fin d → ℂ) × (Fin c → ℂ)) ≃L[ℂ] (Fin (d + c) → ℂ) :=
  (ContinuousLinearEquiv.sumPiEquivProdPi ℂ (Fin d) (Fin c) (fun _ => ℂ)).symm.trans
    (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin (d + c) => ℂ) finSumFinEquiv)

@[simp]
theorem finiteProductCoordinates_left (d c : ℕ) (v : (Fin d → ℂ) × (Fin c → ℂ)) (i : Fin d) :
    finiteProductCoordinates d c v (finSumFinEquiv (Sum.inl i)) = v.1 i := by
  change (Equiv.piCongrLeft (fun _ : Fin (d + c) => ℂ) finSumFinEquiv)
    ((Equiv.sumPiEquivProdPi (fun _ : Fin d ⊕ Fin c => ℂ)).symm v)
    (finSumFinEquiv (Sum.inl i)) = _
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

@[simp]
theorem finiteProductCoordinates_right (d c : ℕ) (v : (Fin d → ℂ) × (Fin c → ℂ)) (i : Fin c) :
    finiteProductCoordinates d c v (finSumFinEquiv (Sum.inr i)) = v.2 i := by
  change (Equiv.piCongrLeft (fun _ : Fin (d + c) => ℂ) finSumFinEquiv)
    ((Equiv.sumPiEquivProdPi (fun _ : Fin d ⊕ Fin c => ℂ)).symm v)
    (finSumFinEquiv (Sum.inr i)) = _
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

theorem finiteProductCoordinates_norm (d c : ℕ) (v : (Fin d → ℂ) × (Fin c → ℂ)) :
    ‖finiteProductCoordinates d c v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j with
    | inl j =>
      rw [finiteProductCoordinates_left, Prod.norm_def]
      exact (norm_le_pi_norm v.1 j).trans (le_max_left _ _)
    | inr j =>
      rw [finiteProductCoordinates_right, Prod.norm_def]
      exact (norm_le_pi_norm v.2 j).trans (le_max_right _ _)
  · rw [Prod.norm_def]
    apply max_le
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      have h := norm_le_pi_norm (finiteProductCoordinates d c v) (finSumFinEquiv (Sum.inl i))
      rwa [finiteProductCoordinates_left] at h
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      have h := norm_le_pi_norm (finiteProductCoordinates d c v) (finSumFinEquiv (Sum.inr i))
      rwa [finiteProductCoordinates_right] at h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.ProductCoordinates.Constructions
