/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleBoundarySquare

/-! # Tuple Alternation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleAlternation

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- Sort an injective tuple with the sign of the sorting permutation, and kill tuples
with repeated entries. -/
def cechTupleAlternatingProjectionBasis {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 1) → ι) : TupleChains.CechTupleChain ι n :=
  if Function.Injective i then
    Finsupp.single (i ∘ Tuple.sort i)
      (Equiv.Perm.sign (Tuple.sort i) : ℤ)
  else
    0

/-- The signed sorting projection on free tuple chains. -/
def cechTupleAlternatingProjection {ι : Type u} [LinearOrder ι] (n : ℕ) :
    TupleChains.CechTupleChain ι n →ₗ[ℤ] TupleChains.CechTupleChain ι n :=
  TupleChains.cechTupleLinearExtension (cechTupleAlternatingProjectionBasis n)

@[simp]
theorem cechTupleAlternatingProjection_single {ι : Type u} [LinearOrder ι] (n : ℕ)
    (i : Fin (n + 1) → ι) (a : ℤ) :
    cechTupleAlternatingProjection n (Finsupp.single i a) =
      a • cechTupleAlternatingProjectionBasis n i := by
  simp [cechTupleAlternatingProjection]

theorem cechTupleAlternatingProjectionBasis_of_injective
    {ι : Type u} [LinearOrder ι] {n : ℕ}
    (i : Fin (n + 1) → ι) (hi : Function.Injective i) :
    cechTupleAlternatingProjectionBasis n i =
      Finsupp.single (i ∘ Tuple.sort i)
        (Equiv.Perm.sign (Tuple.sort i) : ℤ) := by
  simp [cechTupleAlternatingProjectionBasis, hi]

theorem cechTupleAlternatingProjectionBasis_of_not_injective
    {ι : Type u} [LinearOrder ι] {n : ℕ}
    (i : Fin (n + 1) → ι) (hi : ¬Function.Injective i) :
    cechTupleAlternatingProjectionBasis n i = 0 := by
  simp [cechTupleAlternatingProjectionBasis, hi]

theorem cechTupleAlternatingProjectionBasis_comp_perm
    {ι : Type u} [LinearOrder ι] {n : ℕ}
    (i : Fin (n + 1) → ι) (σ : Equiv.Perm (Fin (n + 1))) :
    cechTupleAlternatingProjectionBasis n (i ∘ σ) =
      (Equiv.Perm.sign σ : ℤ) •
        cechTupleAlternatingProjectionBasis n i := by
  by_cases hi : Function.Injective i
  · have hiσ : Function.Injective (i ∘ σ) :=
      (Function.Injective.of_comp_iff' i σ.bijective).2 hi
    rw [cechTupleAlternatingProjectionBasis_of_injective (i ∘ σ) hiσ,
      cechTupleAlternatingProjectionBasis_of_injective i hi,
      Finsupp.smul_single]
    have htuple :
        (i ∘ σ) ∘ Tuple.sort (i ∘ σ) = i ∘ Tuple.sort i :=
      Tuple.comp_perm_comp_sort_eq_comp_sort
    rw [htuple]
    have hperm :
        σ * Tuple.sort (i ∘ σ) = Tuple.sort i := by
      ext k
      exact congrArg Fin.val (hi (congrFun htuple k))
    have hsign := congrArg
      (fun τ : Equiv.Perm (Fin (n + 1)) =>
        (Equiv.Perm.sign τ : ℤ)) hperm
    simp only [Equiv.Perm.sign_mul, Units.val_mul] at hsign
    have hs : (Equiv.Perm.sign σ : ℤ) *
        (Equiv.Perm.sign σ : ℤ) = 1 :=
      Int.units_coe_mul_self (Equiv.Perm.sign σ)
    congr 1
    calc
      (Equiv.Perm.sign (Tuple.sort (i ∘ σ)) : ℤ) =
          1 * (Equiv.Perm.sign (Tuple.sort (i ∘ σ)) : ℤ) := by rw [one_mul]
      _ = ((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ)) *
          (Equiv.Perm.sign (Tuple.sort (i ∘ σ)) : ℤ) := by rw [hs]
      _ = (Equiv.Perm.sign σ : ℤ) *
          ((Equiv.Perm.sign σ : ℤ) *
            (Equiv.Perm.sign (Tuple.sort (i ∘ σ)) : ℤ)) := by
              rw [mul_assoc]
      _ = (Equiv.Perm.sign σ : ℤ) *
          (Equiv.Perm.sign (Tuple.sort i) : ℤ) := by rw [hsign]
  · have hiσ : ¬Function.Injective (i ∘ σ) := by
      simpa only [Function.Injective.of_comp_iff' i σ.bijective] using hi
    rw [cechTupleAlternatingProjectionBasis_of_not_injective (i ∘ σ) hiσ,
      cechTupleAlternatingProjectionBasis_of_not_injective i hi, smul_zero]

theorem cechTupleAlternatingProjectionBasis_of_strictMono
    {ι : Type u} [LinearOrder ι] {n : ℕ}
    (i : Fin (n + 1) → ι) (hi : StrictMono i) :
    cechTupleAlternatingProjectionBasis n i = Finsupp.single i 1 := by
  rw [cechTupleAlternatingProjectionBasis_of_injective i hi.injective]
  have hsort : Tuple.sort i = 1 :=
    Tuple.sort_eq_refl_iff_monotone.2 hi.monotone
  simp [hsort]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleAlternation
