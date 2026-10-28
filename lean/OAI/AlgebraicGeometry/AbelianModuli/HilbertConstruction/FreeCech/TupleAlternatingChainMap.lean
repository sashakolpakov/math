/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleDegenerateBoundary

/-! # Tuple Alternating Chain Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleAlternatingChainMap

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

theorem cechTupleAlternatingProjection_boundary_single
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 2) → ι) :
    TupleChains.cechTupleBoundary n
        (TupleAlternation.cechTupleAlternatingProjection (n + 1) (Finsupp.single i 1)) =
      TupleAlternation.cechTupleAlternatingProjection n
        (TupleChains.cechTupleBoundary n (Finsupp.single i 1)) := by
  by_cases hi : Function.Injective i
  · exact TupleInjectiveBoundary.cechTupleAlternatingProjection_boundary_single_of_injective n i hi
  · exact TupleDegenerateBoundary.cechTupleAlternatingProjection_boundary_single_of_not_injective n i hi

theorem cechTupleAlternatingProjection_boundary_single_smul
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 2) → ι) (a : ℤ) :
    TupleChains.cechTupleBoundary n
        (TupleAlternation.cechTupleAlternatingProjection (n + 1) (Finsupp.single i a)) =
      TupleAlternation.cechTupleAlternatingProjection n
        (TupleChains.cechTupleBoundary n (Finsupp.single i a)) := by
  have h := congrArg (fun x => a • x)
    (cechTupleAlternatingProjection_boundary_single n i)
  simpa using h

/-- Signed sorting is a chain map on free tuple chains. -/
theorem cechTupleAlternatingProjection_boundary
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (x : TupleChains.CechTupleChain ι (n + 1)) :
    TupleChains.cechTupleBoundary n (TupleAlternation.cechTupleAlternatingProjection (n + 1) x) =
      TupleAlternation.cechTupleAlternatingProjection n (TupleChains.cechTupleBoundary n x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single i a =>
      exact cechTupleAlternatingProjection_boundary_single_smul n i a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleAlternatingChainMap
