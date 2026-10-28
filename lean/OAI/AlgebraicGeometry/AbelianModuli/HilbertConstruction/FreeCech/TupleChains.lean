/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.RepeatedTuplePartners
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Tuple Chains -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- The free integral module on tuples of length `n + 1`. -/
abbrev CechTupleChain (ι : Type u) (n : ℕ) :=
  (Fin (n + 1) → ι) →₀ ℤ

/-- Delete one entry from a tuple. -/
def cechTupleDelete {ι : Type u} {n : ℕ}
    (i : Fin (n + 2) → ι) (k : Fin (n + 2)) :
    Fin (n + 1) → ι :=
  i ∘ k.succAbove

/-- Extend a function on tuple generators linearly. -/
def cechTupleLinearExtension {ι : Type u} {n m : ℕ}
    (f : (Fin (n + 1) → ι) → CechTupleChain ι m) :
    CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m :=
  Finsupp.lsum ℤ fun i =>
    LinearMap.toSpanSingleton ℤ (CechTupleChain ι m) (f i)

@[simp]
theorem cechTupleLinearExtension_single {ι : Type u} {n m : ℕ}
    (f : (Fin (n + 1) → ι) → CechTupleChain ι m)
    (i : Fin (n + 1) → ι) (a : ℤ) :
    cechTupleLinearExtension f (Finsupp.single i a) = a • f i := by
  simp [cechTupleLinearExtension]

/-- The alternating deletion boundary of a tuple generator. -/
def cechTupleBoundaryBasis {ι : Type u} (n : ℕ)
    (i : Fin (n + 2) → ι) : CechTupleChain ι n :=
  ∑ k : Fin (n + 2),
    Finsupp.single (cechTupleDelete i k) ((-1 : ℤ) ^ (k : ℕ))

/-- The alternating deletion boundary on free tuple chains. -/
def cechTupleBoundary {ι : Type u} (n : ℕ) :
    CechTupleChain ι (n + 1) →ₗ[ℤ] CechTupleChain ι n :=
  cechTupleLinearExtension (cechTupleBoundaryBasis n)

@[simp]
theorem cechTupleBoundary_single {ι : Type u} (n : ℕ)
    (i : Fin (n + 2) → ι) (a : ℤ) :
    cechTupleBoundary n (Finsupp.single i a) =
      a • cechTupleBoundaryBasis n i := by
  simp [cechTupleBoundary]

/-- Prepend one entry to a tuple. -/
def cechTuplePrepend {ι : Type u} {n : ℕ}
    (i₀ : ι) (i : Fin (n + 1) → ι) : Fin (n + 2) → ι :=
  Fin.cases i₀ i

/-- Prepending a fixed entry, extended to free tuple chains. -/
def cechTuplePrependChain {ι : Type u} (i₀ : ι) (n : ℕ) :
    CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι (n + 1) :=
  cechTupleLinearExtension fun i => Finsupp.single (cechTuplePrepend i₀ i) 1

@[simp]
theorem cechTuplePrependChain_single {ι : Type u} (i₀ : ι) (n : ℕ)
    (i : Fin (n + 1) → ι) (a : ℤ) :
    cechTuplePrependChain i₀ n (Finsupp.single i a) =
      Finsupp.single (cechTuplePrepend i₀ i) a := by
  simp [cechTuplePrependChain]

@[simp]
theorem cechTupleDelete_prepend_zero {ι : Type u} {n : ℕ} (i₀ : ι)
    (i : Fin (n + 1) → ι) :
    cechTupleDelete (cechTuplePrepend i₀ i) 0 = i := by
  funext k
  rfl

@[simp]
theorem cechTupleDelete_prepend_succ {ι : Type u} {n : ℕ} (i₀ : ι)
    (i : Fin (n + 2) → ι) (k : Fin (n + 2)) :
    cechTupleDelete (cechTuplePrepend i₀ i) k.succ =
      cechTuplePrepend i₀ (cechTupleDelete i k) := by
  funext l
  refine Fin.cases ?_ (fun m => ?_) l
  · rfl
  · simp [cechTupleDelete, cechTuplePrepend, Function.comp_apply]

theorem cechTupleDelete_delete {ι : Type u} {n : ℕ}
    (i : Fin (n + 3) → ι) {k : Fin (n + 3)} {l : Fin (n + 2)}
    (hkl : k ≤ l.castSucc) :
    cechTupleDelete (cechTupleDelete i l.succ)
        (k.castLT (lt_of_le_of_lt hkl l.is_lt)) =
      cechTupleDelete (cechTupleDelete i k) l := by
  funext m
  have hδ := CategoryTheory.ConcreteCategory.congr_hom
    (SimplexCategory.δ_comp_δ'' hkl)
  exact congrArg i (hδ m)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleChains
