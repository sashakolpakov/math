/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleContraction

/-! # Tuple Boundary Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleBoundarySquare

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

theorem cechTupleBoundary_boundary_single {ι : Type u} (n : ℕ)
    (i : Fin (n + 3) → ι) :
    TupleChains.cechTupleBoundary n
        (TupleChains.cechTupleBoundary (n + 1) (Finsupp.single i 1)) = 0 := by
  simp only [TupleChains.cechTupleBoundary_single, one_smul]
  unfold TupleChains.cechTupleBoundaryBasis
  rw [map_sum]
  simp only [TupleChains.cechTupleBoundary_single]
  unfold TupleChains.cechTupleBoundaryBasis
  simp only [Finset.smul_sum]
  rw [← Finset.sum_product']
  let P := Fin (n + 3) × Fin (n + 2)
  let T : Finset P := {kl : P | (kl.1 : ℕ) ≤ (kl.2 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl T,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ kl : P, kl ∈ T → P := fun kl hkl =>
    (kl.2.succ, Fin.castLT kl.1
      (lt_of_le_of_lt (Finset.mem_filter.mp hkl).right (Fin.is_lt kl.2)))
  apply Finset.sum_bij φ
  · intro kl hkl
    simp_rw [T, φ, Finset.compl_filter, Finset.mem_filter_univ,
      Fin.val_succ, Fin.val_castLT] at hkl ⊢
    omega
  · rintro ⟨k, l⟩ hkl ⟨k', l'⟩ hkl' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.snd h),
      by simpa [φ] using! congr_arg Prod.fst h⟩
  · rintro ⟨k', l'⟩ hkl'
    simp_rw [T, Finset.compl_filter, Finset.mem_filter_univ,
      not_le] at hkl'
    refine ⟨(Fin.castSucc l', k'.pred (by
      rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hkl')), ?_, ?_⟩
    · simpa [T] using! Nat.le_sub_one_of_lt hkl'
    · simp only [φ, Fin.succ_pred, Fin.castLT_castSucc]
  · rintro ⟨k, l⟩ hkl
    dsimp
    rw [TupleChains.cechTupleDelete_delete i]
    · simp [φ, pow_succ, Finsupp.smul_single, mul_comm]
    · simpa [T] using! hkl

theorem cechTupleBoundary_boundary_single_smul {ι : Type u} (n : ℕ)
    (i : Fin (n + 3) → ι) (a : ℤ) :
    TupleChains.cechTupleBoundary n
        (TupleChains.cechTupleBoundary (n + 1) (Finsupp.single i a)) = 0 := by
  have h := congrArg (fun x => a • x) (cechTupleBoundary_boundary_single n i)
  simpa using h

/-- Consecutive free tuple-chain boundaries compose to zero. -/
theorem cechTupleBoundary_boundary {ι : Type u} (n : ℕ)
    (x : TupleChains.CechTupleChain ι (n + 2)) :
    TupleChains.cechTupleBoundary n (TupleChains.cechTupleBoundary (n + 1) x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single i a => exact cechTupleBoundary_boundary_single_smul n i a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleBoundarySquare
