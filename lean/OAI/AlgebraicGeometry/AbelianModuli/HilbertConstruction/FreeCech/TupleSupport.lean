/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopyIdentity

/-! # Tuple Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- Every tuple occurring in a chain uses indices from `N`. -/
def TupleChains.CechTupleChain.SupportedBy {ι : Type u} {n : ℕ}
    (x : TupleChains.CechTupleChain ι n) (N : Set ι) : Prop :=
  ∀ ⦃i⦄, i ∈ x.support → Set.range i ⊆ N

theorem TupleChains.CechTupleChain.supportedBy_zero {ι : Type u} {n : ℕ} {N : Set ι} :
    TupleChains.CechTupleChain.SupportedBy (0 : TupleChains.CechTupleChain ι n) N := by
  intro i hi
  simp at hi

theorem TupleChains.CechTupleChain.SupportedBy.add {ι : Type u} {n : ℕ} {N : Set ι}
    {x y : TupleChains.CechTupleChain ι n} (hx : TupleChains.CechTupleChain.SupportedBy x N)
    (hy : TupleChains.CechTupleChain.SupportedBy y N) :
    TupleChains.CechTupleChain.SupportedBy (x + y) N := by
  classical
  intro i hi
  rcases Finset.mem_union.mp (Finsupp.support_add hi) with hi | hi
  · exact hx hi
  · exact hy hi

theorem TupleChains.CechTupleChain.SupportedBy.sub {ι : Type u} {n : ℕ} {N : Set ι}
    {x y : TupleChains.CechTupleChain ι n} (hx : TupleChains.CechTupleChain.SupportedBy x N)
    (hy : TupleChains.CechTupleChain.SupportedBy y N) :
    TupleChains.CechTupleChain.SupportedBy (x - y) N := by
  classical
  intro i hi
  rcases Finset.mem_union.mp (Finsupp.support_sub hi) with hi | hi
  · exact hx hi
  · exact hy hi

theorem TupleChains.CechTupleChain.SupportedBy.smul {ι : Type u} {n : ℕ} {N : Set ι}
    {x : TupleChains.CechTupleChain ι n} (hx : TupleChains.CechTupleChain.SupportedBy x N) (a : ℤ) :
    TupleChains.CechTupleChain.SupportedBy (a • x) N := by
  intro i hi
  exact hx (Finsupp.support_smul hi)

theorem TupleChains.CechTupleChain.SupportedBy.mono {ι : Type u} {n : ℕ} {N N' : Set ι}
    {x : TupleChains.CechTupleChain ι n} (hx : TupleChains.CechTupleChain.SupportedBy x N)
    (hNN' : N ⊆ N') :
    TupleChains.CechTupleChain.SupportedBy x N' := by
  intro i hi
  exact (hx hi).trans hNN'

theorem TupleChains.CechTupleChain.supportedBy_single {ι : Type u} {n : ℕ} {N : Set ι}
    (i : Fin (n + 1) → ι) (a : ℤ) (hi : Set.range i ⊆ N) :
    TupleChains.CechTupleChain.SupportedBy (Finsupp.single i a) N := by
  intro j hj
  have hji := Finsupp.support_single_subset hj
  simp only [Finset.mem_singleton] at hji
  subst j
  exact hi

theorem TupleChains.CechTupleChain.supportedBy_sum {ι : Type u} {n : ℕ} {N : Set ι}
    {κ : Type*} (s : Finset κ) (f : κ → TupleChains.CechTupleChain ι n)
    (hf : ∀ k ∈ s, TupleChains.CechTupleChain.SupportedBy (f k) N) :
    TupleChains.CechTupleChain.SupportedBy (∑ k ∈ s, f k) N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [TupleChains.CechTupleChain.supportedBy_zero]
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact (hf k (Finset.mem_insert_self k s)).add
        (ih fun l hl => hf l (Finset.mem_insert_of_mem hl))

theorem TupleChains.CechTupleChain.supportedBy_linearExtension
    {ι : Type u} {n m : ℕ} {N : Set ι}
    (f : (Fin (n + 1) → ι) → TupleChains.CechTupleChain ι m)
    (x : TupleChains.CechTupleChain ι n)
    (hf : ∀ i ∈ x.support, TupleChains.CechTupleChain.SupportedBy (f i) N) :
    TupleChains.CechTupleChain.SupportedBy (TupleChains.cechTupleLinearExtension f x) N := by
  classical
  intro j hj
  rw [TupleChains.cechTupleLinearExtension, Finsupp.lsum_apply] at hj
  change j ∈ (x.sum fun i a => a • f i).support at hj
  obtain ⟨i, hi, hj⟩ :=
    Finset.mem_biUnion.mp (Finsupp.support_sum hj)
  exact hf i hi (Finsupp.support_smul hj)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech
