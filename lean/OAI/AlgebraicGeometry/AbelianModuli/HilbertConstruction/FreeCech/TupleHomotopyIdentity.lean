/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleRecursiveHomotopy

/-! # Tuple Homotopy Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopyIdentity

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- Conrad's recursive homotopy satisfies `∂h + h∂ = p - 1`. -/
theorem cechTupleAlternatingHomotopy_identity
    {ι : Type u} [LinearOrder ι] (n : ℕ)
    (x : TupleChains.CechTupleChain ι n) :
    TupleChains.cechTupleBoundary n (TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n x) +
        TupleRecursiveHomotopy.cechTupleAlternatingHomotopyPrevious n x =
      TupleAlternation.cechTupleAlternatingProjection n x - x := by
  induction n with
  | zero =>
      simp [TupleRecursiveHomotopy.cechTupleAlternatingProjection_zero]
  | succ n ih =>
      induction x using Finsupp.induction_linear with
      | zero => simp
      | add x y hx hy =>
          simp only [map_add]
          calc
            (TupleChains.cechTupleBoundary (n + 1))
                  (TupleRecursiveHomotopy.cechTupleAlternatingHomotopy (n + 1) x) +
                (TupleChains.cechTupleBoundary (n + 1))
                  (TupleRecursiveHomotopy.cechTupleAlternatingHomotopy (n + 1) y) +
              (TupleRecursiveHomotopy.cechTupleAlternatingHomotopyPrevious (n + 1) x +
                TupleRecursiveHomotopy.cechTupleAlternatingHomotopyPrevious (n + 1) y) =
                ((TupleChains.cechTupleBoundary (n + 1))
                    (TupleRecursiveHomotopy.cechTupleAlternatingHomotopy (n + 1) x) +
                  TupleRecursiveHomotopy.cechTupleAlternatingHomotopyPrevious (n + 1) x) +
                ((TupleChains.cechTupleBoundary (n + 1))
                    (TupleRecursiveHomotopy.cechTupleAlternatingHomotopy (n + 1) y) +
                  TupleRecursiveHomotopy.cechTupleAlternatingHomotopyPrevious (n + 1) y) := by
                    abel
            _ = (TupleAlternation.cechTupleAlternatingProjection (n + 1) x - x) +
                (TupleAlternation.cechTupleAlternatingProjection (n + 1) y - y) := by
                  rw [hx, hy]
            _ = TupleAlternation.cechTupleAlternatingProjection (n + 1) x +
                  TupleAlternation.cechTupleAlternatingProjection (n + 1) y -
                (x + y) := by
                  abel
      | single i a =>
          let ω :=
            TupleAlternation.cechTupleAlternatingProjectionBasis (n + 1) i -
              Finsupp.single i 1 -
              TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n
                (TupleChains.cechTupleBoundaryBasis n i)
          have hp := TupleAlternatingChainMap.cechTupleAlternatingProjection_boundary
            (ι := ι) n (Finsupp.single i 1)
          simp only [TupleAlternation.cechTupleAlternatingProjection_single,
            TupleChains.cechTupleBoundary_single, one_smul] at hp
          have hih := ih (TupleChains.cechTupleBoundaryBasis n i)
          rw [TupleRecursiveHomotopy.cechTupleAlternatingHomotopyPrevious_boundaryBasis,
            add_zero] at hih
          have hcycle : TupleChains.cechTupleBoundary n ω = 0 := by
            dsimp only [ω]
            rw [map_sub, map_sub, hp, hih]
            simp only [TupleChains.cechTupleBoundary_single, one_smul]
            abel
          have hcon := TupleContraction.cechTuplePrepend_contraction (i 0) n ω
          rw [hcycle, map_zero, add_zero] at hcon
          have hunit :
              TupleChains.cechTupleBoundary (n + 1)
                    (TupleRecursiveHomotopy.cechTupleAlternatingHomotopy (n + 1)
                      (Finsupp.single i 1)) +
                  TupleRecursiveHomotopy.cechTupleAlternatingHomotopyPrevious (n + 1)
                    (Finsupp.single i 1) =
                TupleAlternation.cechTupleAlternatingProjection (n + 1)
                    (Finsupp.single i 1) -
                  Finsupp.single i 1 := by
            rw [TupleRecursiveHomotopy.cechTupleAlternatingHomotopy_succ_single, one_smul,
              TupleRecursiveHomotopy.cechTupleAlternatingHomotopyPrevious_succ_apply,
              TupleChains.cechTupleBoundary_single, one_smul,
              TupleAlternation.cechTupleAlternatingProjection_single, one_smul]
            change TupleChains.cechTupleBoundary (n + 1)
                (TupleChains.cechTuplePrependChain (i 0) (n + 1) ω) +
                TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n
                  (TupleChains.cechTupleBoundaryBasis n i) =
              TupleAlternation.cechTupleAlternatingProjectionBasis (n + 1) i -
                Finsupp.single i 1
            rw [hcon]
            dsimp only [ω]
            abel
          have h := congrArg (fun y => a • y) hunit
          simpa [smul_sub, Finsupp.smul_single] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopyIdentity
