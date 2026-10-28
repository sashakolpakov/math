/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleAlternatingChainMap

/-! # Tuple Recursive Homotopy -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleRecursiveHomotopy

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- Conrad's recursive chain homotopy from the identity to signed sorting. -/
def cechTupleAlternatingHomotopy {ι : Type u} [LinearOrder ι] :
    (n : ℕ) → TupleChains.CechTupleChain ι n →ₗ[ℤ] TupleChains.CechTupleChain ι (n + 1)
  | 0 => 0
  | n + 1 =>
      TupleChains.cechTupleLinearExtension fun i =>
        TupleChains.cechTuplePrependChain (i 0) (n + 1)
          (TupleAlternation.cechTupleAlternatingProjectionBasis (n + 1) i -
            Finsupp.single i 1 -
            cechTupleAlternatingHomotopy n
              (TupleChains.cechTupleBoundaryBasis n i))

@[simp]
theorem cechTupleAlternatingHomotopy_zero
    {ι : Type u} [LinearOrder ι] :
    TupleRecursiveHomotopy.cechTupleAlternatingHomotopy (ι := ι) 0 = 0 :=
  rfl

@[simp]
theorem cechTupleAlternatingHomotopy_succ_single
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 2) → ι) (a : ℤ) :
    TupleRecursiveHomotopy.cechTupleAlternatingHomotopy (n + 1) (Finsupp.single i a) =
      a • TupleChains.cechTuplePrependChain (i 0) (n + 1)
        (TupleAlternation.cechTupleAlternatingProjectionBasis (n + 1) i -
          Finsupp.single i 1 -
          TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n
            (TupleChains.cechTupleBoundaryBasis n i)) := by
  simp [TupleRecursiveHomotopy.cechTupleAlternatingHomotopy, TupleChains.cechTupleLinearExtension]

/-- The lower-degree term `h∂` in the tuple-chain homotopy identity. -/
def cechTupleAlternatingHomotopyPrevious
    {ι : Type u} [LinearOrder ι] :
    (n : ℕ) → TupleChains.CechTupleChain ι n →ₗ[ℤ] TupleChains.CechTupleChain ι n
  | 0 => 0
  | n + 1 =>
      (TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n).comp (TupleChains.cechTupleBoundary n)

@[simp]
theorem cechTupleAlternatingHomotopyPrevious_zero
    {ι : Type u} [LinearOrder ι] :
    cechTupleAlternatingHomotopyPrevious (ι := ι) 0 = 0 :=
  rfl

@[simp]
theorem cechTupleAlternatingHomotopyPrevious_succ_apply
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (x : TupleChains.CechTupleChain ι (n + 1)) :
    cechTupleAlternatingHomotopyPrevious (n + 1) x =
      TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n (TupleChains.cechTupleBoundary n x) :=
  rfl

theorem cechTupleAlternatingProjection_zero
    {ι : Type u} [LinearOrder ι] (x : TupleChains.CechTupleChain ι 0) :
    TupleAlternation.cechTupleAlternatingProjection 0 x = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single i a =>
      have hi : StrictMono i := by
        intro k l hkl
        omega
      rw [TupleAlternation.cechTupleAlternatingProjection_single,
        TupleAlternation.cechTupleAlternatingProjectionBasis_of_strictMono i hi]
      simp

theorem cechTupleAlternatingHomotopyPrevious_boundaryBasis
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 2) → ι) :
    cechTupleAlternatingHomotopyPrevious n
        (TupleChains.cechTupleBoundaryBasis n i) = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
      change TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n
        (TupleChains.cechTupleBoundary n (TupleChains.cechTupleBoundaryBasis (n + 1) i)) = 0
      have hsq := TupleBoundarySquare.cechTupleBoundary_boundary (ι := ι) n
        (Finsupp.single i 1)
      simp only [TupleChains.cechTupleBoundary_single, one_smul] at hsq
      rw [hsq, map_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleRecursiveHomotopy
