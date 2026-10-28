import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveBlockMatrices
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient

/-! # Block Family Matrices -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices.Local

noncomputable section

section

/-! Simultaneous determinant-one blocks in the actual full local position
coordinates, with their inverse-transpose compatibility. -/

open scoped Classical _root_.Matrix

variable {k : Type} [Field k] {Place : Type} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (e : (Place × Fin 3) ≃ Fin n)

def blockFamilyMatrix (g : Place → Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin n) (Fin n) k :=
  Matrix.reindexRingEquiv k ((Equiv.prodComm (Fin 3) Place).trans e)
    (Matrix.blockDiagonal (fun τ => (g τ).val))

theorem blockFamilyMatrix_one : blockFamilyMatrix e (1 : Place → Matrix.SpecialLinearGroup (Fin 3) k) = 1 := by
  change Matrix.reindexRingEquiv k _ (Matrix.blockDiagonal (1 : Place → Matrix (Fin 3) (Fin 3) k)) = 1
  rw [Matrix.blockDiagonal_one, map_one]

theorem blockFamilyMatrix_mul (g h : Place → Matrix.SpecialLinearGroup (Fin 3) k) :
    blockFamilyMatrix e (g * h) = blockFamilyMatrix e g * blockFamilyMatrix e h := by
  unfold blockFamilyMatrix
  rw [← map_mul, ← Matrix.blockDiagonal_mul]
  rfl

theorem blockFamilyMatrix_det (g : Place → Matrix.SpecialLinearGroup (Fin 3) k) :
    (blockFamilyMatrix e g).det = 1 := by
  change (Matrix.reindex ((Equiv.prodComm (Fin 3) Place).trans e)
    ((Equiv.prodComm (Fin 3) Place).trans e) (Matrix.blockDiagonal (fun τ => (g τ).val))).det = 1
  rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  exact Finset.prod_eq_one (fun τ _ => (g τ).property)

def blockFamilyGL : (Place → Matrix.SpecialLinearGroup (Fin 3) k) →* RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k n where
  toFun g :=
    { val := blockFamilyMatrix e g
      inv := blockFamilyMatrix e g⁻¹
      val_inv := by rw [← blockFamilyMatrix_mul, mul_inv_cancel, blockFamilyMatrix_one]
      inv_val := by rw [← blockFamilyMatrix_mul, inv_mul_cancel, blockFamilyMatrix_one] }
  map_one' := Units.ext (blockFamilyMatrix_one e)
  map_mul' g h := Units.ext (blockFamilyMatrix_mul e g h)

theorem blockFamilyMatrix_entry (g : Place → Matrix.SpecialLinearGroup (Fin 3) k)
    (τ υ : Place) (i j : Fin 3) :
    blockFamilyMatrix e g (e (τ, i)) (e (υ, j)) = if τ = υ then (g τ).val i j else 0 := by
  change (if (e.symm (e (τ, i))).1 = (e.symm (e (υ, j))).1 then
    (g (e.symm (e (τ, i))).1).val (e.symm (e (τ, i))).2 (e.symm (e (υ, j))).2 else 0) = _
  simp only [Equiv.symm_apply_apply]

theorem blockFamilyMatrix_mulVec (g : Place → Matrix.SpecialLinearGroup (Fin 3) k)
    (x : Fin n → k) (τ : Place) (i : Fin 3) :
    (blockFamilyMatrix e g *ᵥ x) (e (τ, i)) = ((g τ).val *ᵥ (fun j => x (e (τ, j)))) i := by
  change (∑ j : Fin n, blockFamilyMatrix e g (e (τ, i)) j * x j) = _
  rw [← e.sum_comp]
  simp [Fintype.sum_prod_type, blockFamilyMatrix_entry, Matrix.mulVec, dotProduct]

theorem blockFamilyGL_inverse_transpose (g : Place → Matrix.SpecialLinearGroup (Fin 3) k) :
    ((blockFamilyGL e g)⁻¹).val.transpose = blockFamilyMatrix e (fun τ => Contragredient.Local.contragredient k (g τ)) := by
  apply Matrix.ext
  intro a b
  obtain ⟨⟨τ, i⟩, rfl⟩ := e.surjective a
  obtain ⟨⟨υ, j⟩, rfl⟩ := e.surjective b
  change blockFamilyMatrix e g⁻¹ (e (υ, j)) (e (τ, i)) = _
  rw [blockFamilyMatrix_entry, blockFamilyMatrix_entry]
  by_cases h : τ = υ
  · subst υ
    rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem blockFamilyGL_dual_inverse_transpose (g : Place → Matrix.SpecialLinearGroup (Fin 3) k) :
    ((blockFamilyGL e (fun τ => Contragredient.Local.contragredient k (g τ)))⁻¹).val.transpose = blockFamilyMatrix e g := by
  rw [blockFamilyGL_inverse_transpose]
  congr 1
  funext τ
  exact Contragredient.Local.contragredient_involutive k (g τ)

end

/-! The position-momentum convention turns the inverse-transpose position
blocks into the native rational unitary symplectic blocks. -/

open scoped Classical _root_.Matrix

variable {k : Type} [Field k] {n : ℕ}

theorem swapped_levi_action (A : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k n) (x : Sum (Fin n) (Fin n) → k) :
    (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic A)).val *ᵥ x =
      Sum.elim (((A⁻¹).val.transpose) *ᵥ (fun i => x (Sum.inl i)))
        (A.val *ᵥ (fun i => x (Sum.inr i))) := by
  rw [RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom_action, RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic_matrix, Matrix.fromBlocks_mulVec]
  funext i
  cases i <;> simp [RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.swapPhase]

variable {Place : Type} [Fintype Place] [DecidableEq Place] (e : (Place × Fin 3) ≃ Fin n)

def blockFamilySymplectic (g : Place → Matrix.SpecialLinearGroup (Fin 3) k) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Place × Fin 3) k :=
  RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e.symm
    (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic (blockFamilyGL e (fun τ => Contragredient.Local.contragredient k (g τ)))))

theorem blockFamilySymplectic_inl [TopologicalSpace k]
    (g : Place → Matrix.SpecialLinearGroup (Fin 3) k)
    (x : Sum (Place × Fin 3) (Place × Fin 3) → k) (τ : Place) (i : Fin 3) :
    ((blockFamilySymplectic e g).val *ᵥ x) (Sum.inl (τ, i)) =
      ((g τ).val *ᵥ (fun j => x (Sum.inl (τ, j)))) i := by
  have h := RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex_inverse_action e
    (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic (blockFamilyGL e (fun τ => Contragredient.Local.contragredient k (g τ))))) x
  rw [swapped_levi_action, blockFamilyGL_dual_inverse_transpose] at h
  have h' := congrFun h (Sum.inl (e (τ, i)))
  change ((blockFamilySymplectic e g).val *ᵥ x) (Sum.inl (e.symm (e (τ, i)))) =
    (blockFamilyMatrix e g *ᵥ (fun j => x (Sum.inl (e.symm j)))) (e (τ, i)) at h'
  rw [Equiv.symm_apply_apply, blockFamilyMatrix_mulVec] at h'
  simpa only [Equiv.symm_apply_apply] using h'

theorem blockFamilySymplectic_inr [TopologicalSpace k]
    (g : Place → Matrix.SpecialLinearGroup (Fin 3) k)
    (x : Sum (Place × Fin 3) (Place × Fin 3) → k) (τ : Place) (i : Fin 3) :
    ((blockFamilySymplectic e g).val *ᵥ x) (Sum.inr (τ, i)) =
      ((g τ)⁻¹).val.transpose.mulVec (fun j => x (Sum.inr (τ, j))) i := by
  have h := RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex_inverse_action e
    (RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic (blockFamilyGL e (fun τ => Contragredient.Local.contragredient k (g τ))))) x
  rw [swapped_levi_action] at h
  have h' := congrFun h (Sum.inr (e (τ, i)))
  change ((blockFamilySymplectic e g).val *ᵥ x) (Sum.inr (e.symm (e (τ, i)))) =
    (blockFamilyMatrix e (fun τ => Contragredient.Local.contragredient k (g τ)) *ᵥ
      (fun j => x (Sum.inr (e.symm j)))) (e (τ, i)) at h'
  rw [Equiv.symm_apply_apply, blockFamilyMatrix_mulVec] at h'
  have hd : (Contragredient.Local.contragredient k (g τ)).val = ((g τ)⁻¹).val.transpose := rfl
  simpa only [Equiv.symm_apply_apply, hd] using h'

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BlockFamilyMatrices.Local
