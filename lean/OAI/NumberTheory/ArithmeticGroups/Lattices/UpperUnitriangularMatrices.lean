import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousEndMatrixEquiv
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Upper Unitriangular Matrices -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnitriangularMatrices.Construction

noncomputable section

/-! Upper unitriangular matrices are stable under multiplication and
inversion, and their bounded coordinate subsets are compact in GL. -/

open Set _root_.Matrix
open scoped Classical _root_.Matrix.Norms.Operator

def IsUpperUnitriangular {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  M.IsUpperTriangular ∧ ∀ i, M i i = 1

theorem upper_triangular_mul_diagonal {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsUpperTriangular) (hN : N.IsUpperTriangular)
    (i : Fin n) : (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · simp

theorem IsUpperUnitriangular.mul {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsUpperUnitriangular M) (hN : IsUpperUnitriangular N) : IsUpperUnitriangular (M * N) :=
  ⟨hM.1.mul hN.1, fun i => by rw [upper_triangular_mul_diagonal M N hM.1 hN.1, hM.2, hN.2, one_mul]⟩

theorem IsUpperUnitriangular.det {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsUpperUnitriangular M) : M.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular hM.1]
  simp only [hM.2, Finset.prod_const_one]

theorem IsUpperUnitriangular.isUnit {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsUpperUnitriangular M) : IsUnit M :=
  M.isUnit_iff_isUnit_det.mpr (hM.det.symm ▸ isUnit_one)

theorem IsUpperUnitriangular.unit_inv {n : ℕ} (g : (Matrix (Fin n) (Fin n) ℝ)ˣ)
    (hg : IsUpperUnitriangular g.val) : IsUpperUnitriangular (g⁻¹).val := by
  let : Invertible g.val := g.invertible
  have htri : (g⁻¹).val.IsUpperTriangular := by
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg.1
  refine ⟨htri, fun i => ?_⟩
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) g.val_inv
  change (g.val * (g⁻¹).val) i i = (1 : Matrix (Fin n) (Fin n) ℝ) i i at he
  rw [upper_triangular_mul_diagonal _ _ hg.1 htri, hg.2, one_mul, Matrix.one_apply_eq] at he
  exact he

theorem isClosed_upper_unitriangular (n : ℕ) :
    IsClosed {M : Matrix (Fin n) (Fin n) ℝ | IsUpperUnitriangular M} := by
  have hu : IsClosed {M : Matrix (Fin n) (Fin n) ℝ | ∀ i j, j < i → M i j = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  have hd : IsClosed {M : Matrix (Fin n) (Fin n) ℝ | ∀ i, M i i = 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i =>
      isClosed_eq ((continuous_apply i).comp (continuous_apply i)) continuous_const
  exact hu.inter hd

theorem bounded_upper_unitriangular_isCompact (n : ℕ) (c : ℝ) :
    IsCompact {g : (Matrix (Fin n) (Fin n) ℝ)ˣ |
      IsUpperUnitriangular g.val ∧ ∀ i j, |g.val i j| ≤ c} := by
  let C : Set (Matrix (Fin n) (Fin n) ℝ) := {M | IsUpperUnitriangular M ∧ ∀ i j, |M i j| ≤ c}
  have hc : IsClosed C := by
    change IsClosed ({M : Matrix (Fin n) (Fin n) ℝ | IsUpperUnitriangular M} ∩
      {M : Matrix (Fin n) (Fin n) ℝ | ∀ i j, |M i j| ≤ c})
    apply (isClosed_upper_unitriangular n).inter
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (((continuous_apply j).comp (continuous_apply i)).abs) continuous_const
  have hbox : IsCompact (Set.pi Set.univ (fun _ : Fin n =>
      Set.pi Set.univ (fun _ : Fin n => Set.Icc (-c) c))) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  have hC : IsCompact C := hbox.of_isClosed_subset hc (by
    intro M hM i _ j _
    exact abs_le.mp (hM.2 i j))
  apply Units.isOpenEmbedding_val.isEmbedding.isInducing.isCompact_preimage' hC
  intro M hM
  exact hM.1.isUnit

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnitriangularMatrices.Construction
