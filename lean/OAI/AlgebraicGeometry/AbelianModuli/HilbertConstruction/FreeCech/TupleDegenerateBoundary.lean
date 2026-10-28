/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleInjectiveBoundary

/-! # Tuple Degenerate Boundary -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleDegenerateBoundary

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

theorem cechTupleAlternatingProjectionBasis_delete_pair
    {ι : Type u} [LinearOrder ι] {n : ℕ}
    (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hkl : i k = i l) :
    TupleAlternation.cechTupleAlternatingProjectionBasis n (TupleChains.cechTupleDelete i k) =
      (Equiv.Perm.sign
          (Cech.DeletedTupleSigns.cechDeleteSwapPerm k l) : ℤ) •
        TupleAlternation.cechTupleAlternatingProjectionBasis n (TupleChains.cechTupleDelete i l) := by
  let ρ := Cech.DeletedTupleSigns.cechDeleteSwapPerm k l
  have htuple :
      TupleChains.cechTupleDelete i l ∘ ρ = TupleChains.cechTupleDelete i k :=
    Cech.DeletedTupleSigns.comp_succAbove_cechDeleteSwapPerm_of_eq
      i k l hkl
  have hperm :=
    TupleAlternation.cechTupleAlternatingProjectionBasis_comp_perm
      (TupleChains.cechTupleDelete i l) ρ
  rwa [htuple] at hperm

theorem cechTupleAlternatingProjectionBasis_delete_pair_cancel
    {ι : Type u} [LinearOrder ι] {n : ℕ}
    (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hki : i k = i l) (hkl : k ≠ l) :
    (-1 : ℤ) ^ (k : ℕ) •
        TupleAlternation.cechTupleAlternatingProjectionBasis n (TupleChains.cechTupleDelete i k) +
      (-1 : ℤ) ^ (l : ℕ) •
        TupleAlternation.cechTupleAlternatingProjectionBasis n (TupleChains.cechTupleDelete i l) = 0 := by
  let t := TupleAlternation.cechTupleAlternatingProjectionBasis n (TupleChains.cechTupleDelete i l)
  have hpair :=
    cechTupleAlternatingProjectionBasis_delete_pair i k l hki
  change (-1 : ℤ) ^ (k : ℕ) • _ + (-1 : ℤ) ^ (l : ℕ) • t = 0
  rw [hpair, smul_smul,
    Cech.DeletedTupleSigns.cechDeleteSwapPerm_sign k l hkl]
  have hcoef :
      (-1 : ℤ) ^ (k : ℕ) *
          -((-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (l : ℕ)) =
        -((-1 : ℤ) ^ (l : ℕ)) := by
    rw [mul_neg, ← mul_assoc, ← pow_add,
      (Even.add_self (k : ℕ)).neg_one_pow, one_mul]
  rw [hcoef, neg_smul, neg_add_cancel]

theorem cechTupleAlternatingProjection_boundary_single_of_not_injective
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 2) → ι) (hi : ¬Function.Injective i) :
    TupleChains.cechTupleBoundary n
        (TupleAlternation.cechTupleAlternatingProjection (n + 1) (Finsupp.single i 1)) =
      TupleAlternation.cechTupleAlternatingProjection n
        (TupleChains.cechTupleBoundary n (Finsupp.single i 1)) := by
  rw [TupleAlternation.cechTupleAlternatingProjection_single,
    TupleAlternation.cechTupleAlternatingProjectionBasis_of_not_injective i hi, one_smul,
    map_zero, TupleChains.cechTupleBoundary_single, one_smul]
  unfold TupleChains.cechTupleBoundaryBasis
  rw [map_sum]
  simp only [TupleAlternation.cechTupleAlternatingProjection_single]
  symm
  let F : Fin (n + 2) → TupleChains.CechTupleChain ι n := fun k =>
    (-1 : ℤ) ^ (k : ℕ) •
      TupleAlternation.cechTupleAlternatingProjectionBasis n (TupleChains.cechTupleDelete i k)
  change ∑ k, F k = 0
  by_cases hall : ∀ k : Fin (n + 2),
      ¬Function.Injective (TupleChains.cechTupleDelete i k)
  · apply Finset.sum_eq_zero
    intro k _
    dsimp only [F]
    rw [TupleAlternation.cechTupleAlternatingProjectionBasis_of_not_injective _ (hall k),
      smul_zero]
  · have hex : ∃ k : Fin (n + 2),
        Function.Injective (TupleChains.cechTupleDelete i k) := by
      by_contra h
      apply hall
      intro k hk
      exact h ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hex
    obtain ⟨l, hlk, hil⟩ :=
      Cech.RepeatedTuplePartners.exists_partner_of_delete_injective
        i hi k hk
    have hkl : k ≠ l := hlk.symm
    have hother (m : Fin (n + 2)) (hmk : m ≠ k) (hml : m ≠ l) :
        F m = 0 := by
      have hm :=
        Cech.RepeatedTuplePartners.delete_not_injective_of_ne
          i k l m hkl hmk.symm hml.symm hil
      have hm' : ¬Function.Injective (TupleChains.cechTupleDelete i m) := by
        simpa [TupleChains.cechTupleDelete] using hm
      dsimp only [F]
      rw [TupleAlternation.cechTupleAlternatingProjectionBasis_of_not_injective _ hm',
        smul_zero]
    have hrem : ((Finset.univ.erase l).erase k).sum F = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hmk : m ≠ k := (Finset.mem_erase.mp hm).1
      have hml : m ≠ l :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1
      exact hother m hmk hml
    have hk_mem : k ∈ Finset.univ.erase l :=
      Finset.mem_erase.mpr ⟨hkl, Finset.mem_univ k⟩
    calc
      ∑ m, F m = (Finset.univ.erase l).sum F + F l :=
        (Finset.sum_erase_add Finset.univ F (Finset.mem_univ l)).symm
      _ = (((Finset.univ.erase l).erase k).sum F + F k) + F l := by
        rw [Finset.sum_erase_add (Finset.univ.erase l) F hk_mem]
      _ = F k + F l := by rw [hrem, zero_add]
      _ = 0 := by
        dsimp only [F]
        exact cechTupleAlternatingProjectionBasis_delete_pair_cancel
          i k l hil.symm hkl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleDegenerateBoundary
