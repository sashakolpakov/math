/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TuplePermutationFaces

/-! # Tuple Injective Boundary -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleInjectiveBoundary

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

theorem cechTupleAlternatingProjection_boundary_single_of_injective
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 2) → ι) (hi : Function.Injective i) :
    TupleChains.cechTupleBoundary n
        (TupleAlternation.cechTupleAlternatingProjection (n + 1) (Finsupp.single i 1)) =
      TupleAlternation.cechTupleAlternatingProjection n
        (TupleChains.cechTupleBoundary n (Finsupp.single i 1)) := by
  let σ := Tuple.sort i
  let j := i ∘ σ
  have hj : StrictMono j :=
    (Tuple.monotone_sort i).strictMono_of_injective
      (hi.comp σ.injective)
  rw [TupleAlternation.cechTupleAlternatingProjection_single,
    TupleAlternation.cechTupleAlternatingProjectionBasis_of_injective i hi, one_smul,
    TupleChains.cechTupleBoundary_single]
  rw [TupleChains.cechTupleBoundary_single, one_smul]
  change (Equiv.Perm.sign σ : ℤ) • TupleChains.cechTupleBoundaryBasis n j =
    TupleAlternation.cechTupleAlternatingProjection n (TupleChains.cechTupleBoundaryBasis n i)
  unfold TupleChains.cechTupleBoundaryBasis
  rw [map_sum, Finset.smul_sum]
  simp only [TupleAlternation.cechTupleAlternatingProjection_single]
  refine Fintype.sum_equiv σ _ _ fun r => ?_
  rw [TuplePermutationFaces.cechTupleAlternatingProjectionBasis_delete_perm i σ hj r]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  congr 1
  rw [Cech.PermutedTupleSigns.cechPermDelete_sign]
  have hsquare :
      (-1 : ℤ) ^ (σ r : ℕ) * (-1 : ℤ) ^ (σ r : ℕ) = 1 := by
    rw [← pow_add, (Even.add_self (σ r : ℕ)).neg_one_pow]
  calc
    (Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ (r : ℕ) =
        (-1 : ℤ) ^ (r : ℕ) * (Equiv.Perm.sign σ : ℤ) := mul_comm _ _
    _ = (-1 : ℤ) ^ (σ r : ℕ) *
        (((-1 : ℤ) ^ (r : ℕ) * (Equiv.Perm.sign σ : ℤ)) *
          (-1 : ℤ) ^ (σ r : ℕ)) := by
      symm
      calc
        (-1 : ℤ) ^ (σ r : ℕ) *
            (((-1 : ℤ) ^ (r : ℕ) * (Equiv.Perm.sign σ : ℤ)) *
              (-1 : ℤ) ^ (σ r : ℕ)) =
            (((-1 : ℤ) ^ (σ r : ℕ)) *
              (-1 : ℤ) ^ (σ r : ℕ)) *
              (((-1 : ℤ) ^ (r : ℕ)) *
                (Equiv.Perm.sign σ : ℤ)) := by ring
        _ = (-1 : ℤ) ^ (r : ℕ) * (Equiv.Perm.sign σ : ℤ) := by
          rw [hsquare, one_mul]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleInjectiveBoundary
