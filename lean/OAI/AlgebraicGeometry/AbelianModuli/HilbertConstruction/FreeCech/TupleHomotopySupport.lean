/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleSupportOperations

/-! # Tuple Homotopy Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

theorem cechTupleAlternatingHomotopy_supportedBy
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (x : TupleChains.CechTupleChain ι n) (N : Set ι)
    (hx : TupleChains.CechTupleChain.SupportedBy x N) :
    TupleChains.CechTupleChain.SupportedBy
      (TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n x) N := by
  induction n generalizing N with
  | zero =>
      change TupleChains.CechTupleChain.SupportedBy 0 N
      exact TupleChains.CechTupleChain.supportedBy_zero
  | succ n ih =>
      rw [TupleRecursiveHomotopy.cechTupleAlternatingHomotopy]
      apply TupleChains.CechTupleChain.supportedBy_linearExtension
      intro i hi
      have hiN : Set.range i ⊆ N := hx hi
      have hp :=
        (TupleSupportOperations.cechTupleAlternatingProjectionBasis_supportedBy (n + 1) i).mono hiN
      have hsingle :=
        (TupleChains.CechTupleChain.supportedBy_single i 1 (Subset.rfl)).mono hiN
      have hboundary :=
        (TupleSupportOperations.cechTupleBoundaryBasis_supportedBy n i).mono hiN
      have hh := ih _ _ hboundary
      apply TupleSupportOperations.cechTuplePrependChain_supportedBy
      · exact hiN ⟨0, rfl⟩
      · exact (hp.sub hsingle).sub hh

/-- A free tuple-chain map does not introduce new tuple indices. -/
def CechTupleSupportNonincreasing
    {ι : Type u} {n m : ℕ}
    (f : TupleChains.CechTupleChain ι n →ₗ[ℤ] TupleChains.CechTupleChain ι m) : Prop :=
  ∀ i : Fin (n + 1) → ι,
    TupleChains.CechTupleChain.SupportedBy (f (Finsupp.single i 1)) (Set.range i)

theorem cechTupleAlternatingHomotopy_supportNonincreasing
    {ι : Type u} [LinearOrder ι] (n : ℕ) :
    CechTupleSupportNonincreasing
      (TupleRecursiveHomotopy.cechTupleAlternatingHomotopy (ι := ι) n) := by
  intro i
  apply cechTupleAlternatingHomotopy_supportedBy
  exact TupleChains.CechTupleChain.supportedBy_single i 1 Subset.rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport
