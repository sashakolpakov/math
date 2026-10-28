/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains

/-! # Tuple Contraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleContraction

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

theorem cechTuplePrepend_contraction_single {ι : Type u} (i₀ : ι) (n : ℕ)
    (i : Fin (n + 2) → ι) :
    TupleChains.cechTupleBoundary (n + 1)
          (TupleChains.cechTuplePrependChain i₀ (n + 1) (Finsupp.single i 1)) +
        TupleChains.cechTuplePrependChain i₀ n
          (TupleChains.cechTupleBoundary n (Finsupp.single i 1)) =
      Finsupp.single i 1 := by
  simp only [TupleChains.cechTuplePrependChain_single, TupleChains.cechTupleBoundary_single, one_smul]
  unfold TupleChains.cechTupleBoundaryBasis
  rw [Fin.sum_univ_succ, map_sum]
  simp only [Fin.val_zero, pow_zero, TupleChains.cechTupleDelete_prepend_zero,
    TupleChains.cechTuplePrependChain_single, Fin.val_succ, pow_succ,
    TupleChains.cechTupleDelete_prepend_succ, mul_neg, mul_one, Finsupp.single_neg]
  rw [Finset.sum_neg_distrib]
  abel

theorem cechTuplePrepend_contraction_single_smul {ι : Type u} (i₀ : ι) (n : ℕ)
    (i : Fin (n + 2) → ι) (a : ℤ) :
    TupleChains.cechTupleBoundary (n + 1)
          (TupleChains.cechTuplePrependChain i₀ (n + 1) (Finsupp.single i a)) +
        TupleChains.cechTuplePrependChain i₀ n
          (TupleChains.cechTupleBoundary n (Finsupp.single i a)) =
      Finsupp.single i a := by
  have h := congrArg (fun x => a • x) (cechTuplePrepend_contraction_single i₀ n i)
  simpa using h

/-- Prepending a fixed entry contracts the free tuple-chain complex in positive degrees. -/
theorem cechTuplePrepend_contraction {ι : Type u} (i₀ : ι) (n : ℕ)
    (x : TupleChains.CechTupleChain ι (n + 1)) :
    TupleChains.cechTupleBoundary (n + 1) (TupleChains.cechTuplePrependChain i₀ (n + 1) x) +
        TupleChains.cechTuplePrependChain i₀ n (TupleChains.cechTupleBoundary n x) = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add]
      calc
        _ =
            (TupleChains.cechTupleBoundary (n + 1) (TupleChains.cechTuplePrependChain i₀ (n + 1) x) +
              TupleChains.cechTuplePrependChain i₀ n (TupleChains.cechTupleBoundary n x)) +
            (TupleChains.cechTupleBoundary (n + 1) (TupleChains.cechTuplePrependChain i₀ (n + 1) y) +
              TupleChains.cechTuplePrependChain i₀ n (TupleChains.cechTupleBoundary n y)) := by
                abel
        _ = x + y := by rw [hx, hy]
  | single i a => exact cechTuplePrepend_contraction_single_smul i₀ n i a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleContraction
