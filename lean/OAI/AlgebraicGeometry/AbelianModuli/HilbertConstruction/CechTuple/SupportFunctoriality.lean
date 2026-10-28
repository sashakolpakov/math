/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionMaps

/-! # Support Functoriality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- The identity tuple-chain map does not enlarge support. -/
theorem CechTuple.SupportFunctoriality.cechTupleSupportNonincreasing_id
    {ι : Type u} {n : ℕ} :
    FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing
      (LinearMap.id : FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι n) := by
  intro i
  simpa using FreeCech.TupleChains.CechTupleChain.supportedBy_single i 1 Subset.rfl

/-- A sum of support-nonincreasing tuple-chain maps is support-nonincreasing. -/
theorem FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.add
    {ι : Type u} {n m : ℕ}
    {f g : FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι m}
    (hf : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f)
    (hg : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing g) :
    FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing (f + g) := by
  intro i
  simpa using (hf i).add (hg i)

/-- A negated support-nonincreasing tuple-chain map is support-nonincreasing. -/
theorem FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.neg
    {ι : Type u} {n m : ℕ}
    {f : FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι m}
    (hf : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f) :
    FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing (-f) := by
  intro i
  simpa using (hf i).smul (-1)

/-- A linear map out of a free integral module is the sum of its values on basis vectors. -/
theorem CechTuple.SupportFunctoriality.linearMap_apply_eq_finsupp_sum_single
    {α N : Type u} [AddCommGroup N]
    (f : (α →₀ ℤ) →ₗ[ℤ] N) (x : α →₀ ℤ) :
    f x = x.sum fun i a => a • f (Finsupp.single i 1) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, hx, hy,
        Finsupp.sum_add_index (by simp) (by simp [add_smul])]
  | single i a =>
      calc
        f (Finsupp.single i a) =
            a • f (Finsupp.single i 1) := by
          simpa using f.map_smul a (Finsupp.single i 1)
        _ = (Finsupp.single i a).sum
            (fun j b => b • f (Finsupp.single j 1)) := by
          simp

/-- A support-nonincreasing map preserves any prescribed containing support. -/
theorem FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.map_supportedBy
    {ι : Type u} {n m : ℕ}
    {f : FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι m}
    (hf : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f)
    (x : FreeCech.TupleChains.CechTupleChain ι n) (N : Set ι)
    (hx : FreeCech.TupleChains.CechTupleChain.SupportedBy x N) :
    FreeCech.TupleChains.CechTupleChain.SupportedBy (f x) N := by
  rw [CechTuple.SupportFunctoriality.linearMap_apply_eq_finsupp_sum_single]
  change FreeCech.TupleChains.CechTupleChain.SupportedBy
    (∑ i ∈ x.support,
      x i • f (Finsupp.single i 1)) N
  apply FreeCech.TupleChains.CechTupleChain.supportedBy_sum x.support _
  intro i hi
  exact FreeCech.TupleChains.CechTupleChain.SupportedBy.smul
    (FreeCech.TupleChains.CechTupleChain.SupportedBy.mono (hf i) (hx hi)) (x i)

/-- A composite of support-nonincreasing tuple-chain maps is support-nonincreasing. -/
theorem FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.comp
    {ι : Type u} {n m l : ℕ}
    {f : FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι m}
    {g : FreeCech.TupleChains.CechTupleChain ι m →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι l}
    (hg : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing g)
    (hf : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f) :
    FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing (g.comp f) := by
  intro i
  exact FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.map_supportedBy
    hg (f (Finsupp.single i 1)) (Set.range i) (hf i)

/-- The tuple deletion boundary does not enlarge support. -/
theorem CechTuple.SupportFunctoriality.cechTupleBoundary_supportNonincreasing
    {ι : Type u} (n : ℕ) :
    FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing
      (FreeCech.TupleChains.cechTupleBoundary (ι := ι) n) := by
  intro i
  apply FreeCech.TupleSupportOperations.cechTupleBoundary_supportedBy
  exact FreeCech.TupleChains.CechTupleChain.supportedBy_single i 1 Subset.rfl

/-- The sorted-tuple projection does not enlarge support. -/
theorem CechTuple.SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing
    {ι : Type u} [LinearOrder ι] (n : ℕ) :
    FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing
      (FreeCech.TupleAlternation.cechTupleAlternatingProjection (ι := ι) n) := by
  intro i
  apply FreeCech.TupleSupportOperations.cechTupleAlternatingProjection_supportedBy
  exact FreeCech.TupleChains.CechTupleChain.supportedBy_single i 1 Subset.rfl

/-- The lower-degree term in the tuple homotopy does not enlarge support. -/
theorem CechTuple.SupportFunctoriality.cechTupleAlternatingHomotopyPrevious_supportNonincreasing
    {ι : Type u} [LinearOrder ι] (n : ℕ) :
    FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing
      (FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopyPrevious (ι := ι) n) := by
  intro i
  cases n with
  | zero =>
      exact FreeCech.TupleChains.CechTupleChain.supportedBy_zero
  | succ n =>
      apply FreeCech.TupleHomotopySupport.cechTupleAlternatingHomotopy_supportedBy
      apply FreeCech.TupleSupportOperations.cechTupleBoundary_supportedBy
      exact FreeCech.TupleChains.CechTupleChain.supportedBy_single i 1 Subset.rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
