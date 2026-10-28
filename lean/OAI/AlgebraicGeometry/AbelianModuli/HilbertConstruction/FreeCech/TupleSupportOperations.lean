/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleSupport

/-! # Tuple Support Operations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleSupportOperations

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

theorem cechTupleBoundaryBasis_supportedBy
    {ι : Type u} (n : ℕ) (i : Fin (n + 2) → ι) :
    TupleChains.CechTupleChain.SupportedBy (TupleChains.cechTupleBoundaryBasis n i)
      (Set.range i) := by
  unfold TupleChains.cechTupleBoundaryBasis
  refine TupleChains.CechTupleChain.supportedBy_sum Finset.univ _ ?_
  intro k _
  apply TupleChains.CechTupleChain.supportedBy_single
  rintro x ⟨l, rfl⟩
  exact ⟨k.succAbove l, rfl⟩

theorem cechTupleAlternatingProjectionBasis_supportedBy
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 1) → ι) :
    TupleChains.CechTupleChain.SupportedBy
      (TupleAlternation.cechTupleAlternatingProjectionBasis n i) (Set.range i) := by
  by_cases hi : Function.Injective i
  · rw [TupleAlternation.cechTupleAlternatingProjectionBasis_of_injective i hi]
    apply TupleChains.CechTupleChain.supportedBy_single
    rintro x ⟨k, rfl⟩
    exact ⟨Tuple.sort i k, rfl⟩
  · rw [TupleAlternation.cechTupleAlternatingProjectionBasis_of_not_injective i hi]
    exact TupleChains.CechTupleChain.supportedBy_zero

theorem cechTuplePrependChain_supportedBy
    {ι : Type u} (i₀ : ι) (n : ℕ)
    (x : TupleChains.CechTupleChain ι n) (N : Set ι)
    (hi₀ : i₀ ∈ N) (hx : TupleChains.CechTupleChain.SupportedBy x N) :
    TupleChains.CechTupleChain.SupportedBy (TupleChains.cechTuplePrependChain i₀ n x) N := by
  rw [TupleChains.cechTuplePrependChain]
  apply TupleChains.CechTupleChain.supportedBy_linearExtension
  intro i hi
  apply TupleChains.CechTupleChain.supportedBy_single
  rintro y ⟨k, rfl⟩
  induction k using Fin.cases with
  | zero => exact hi₀
  | succ l => exact hx hi ⟨l, rfl⟩

theorem cechTupleBoundary_supportedBy
    {ι : Type u} (n : ℕ) (x : TupleChains.CechTupleChain ι (n + 1))
    (N : Set ι) (hx : TupleChains.CechTupleChain.SupportedBy x N) :
    TupleChains.CechTupleChain.SupportedBy (TupleChains.cechTupleBoundary n x) N := by
  rw [TupleChains.cechTupleBoundary]
  apply TupleChains.CechTupleChain.supportedBy_linearExtension
  intro i hi
  exact (cechTupleBoundaryBasis_supportedBy n i).mono (hx hi)

theorem cechTupleAlternatingProjection_supportedBy
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (x : TupleChains.CechTupleChain ι n) (N : Set ι)
    (hx : TupleChains.CechTupleChain.SupportedBy x N) :
    TupleChains.CechTupleChain.SupportedBy
      (TupleAlternation.cechTupleAlternatingProjection n x) N := by
  rw [TupleAlternation.cechTupleAlternatingProjection]
  apply TupleChains.CechTupleChain.supportedBy_linearExtension
  intro i hi
  exact (cechTupleAlternatingProjectionBasis_supportedBy n i).mono (hx hi)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleSupportOperations
