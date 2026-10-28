/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupportAlternating

/-! # Laurent Weight Finite -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective

noncomputable section

open _root_.MvPolynomial
open _root_.AlgebraicGeometry _root_.CategoryTheory
universe u
variable {σ : Type}
local instance LaurentWeightFinite.MvPolynomial.laurentFiniteDecEq : DecidableEq σ := Classical.decEq σ

/-- The negative coordinates of a global homogeneous Laurent exponent, lifted to the ordered-Cech
index universe. -/
def LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.liftedNegativeSupport {d : ℤ}
    (e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) : Set (ULift.{u} σ) :=
  {i | e.1 i.down < 0}

/-- A global homogeneous Laurent exponent is allowed on an ordered tuple exactly when that tuple
contains every coordinate on which the exponent is negative. -/
theorem LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.isAllowedOn_iff_liftedNegativeSupport_subset
    [LinearOrder σ] {d : ℤ} (e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    e.IsAllowedOn (fun k => (a.1 k).down) ↔
      e.liftedNegativeSupport ⊆ Set.range a.1 := by
  constructor
  · intro h i hi
    obtain ⟨k, hk⟩ := h hi
    refine ⟨k, ?_⟩
    apply ULift.ext
    exact hk
  · intro h i hi
    obtain ⟨k, hk⟩ := h (show e.1 (ULift.up i).down < 0 by exact hi)
    refine ⟨k, ?_⟩
    exact congrArg ULift.down hk

/-- For fixed total degree and finitely many coordinates, there are only finitely many homogeneous
Laurent exponents that are negative in every coordinate. -/
theorem LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_univ
    [Fintype σ] (d : ℤ) :
    {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d |
      e.liftedNegativeSupport = Set.univ}.Finite := by
  classical
  apply Set.Finite.of_finite_image
      (f := fun e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d => (e.1 : σ → ℤ))
  · apply (Set.Finite.pi' fun _ => Set.finite_Icc d (-1)).subset
    rintro f ⟨e, he, rfl⟩
    intro i
    have hneg (j : σ) : e.1 j < 0 := by
      have hj : ULift.up j ∈ e.liftedNegativeSupport := by
        rw [he]
        exact Set.mem_univ _
      exact hj
    have hrest : ∑ j ∈ Finset.univ.erase i, e.1 j ≤ 0 := by
      apply Finset.sum_nonpos
      intro j _
      exact (hneg j).le
    have hsum : ∑ j, e.1 j = d := by
      rw [← Finsupp.degree_eq_sum]
      exact e.2
    have hi : i ∈ (Finset.univ : Finset σ) := Finset.mem_univ i
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset σ)
      (fun j => e.1 j) hi
    simp only [Set.mem_Icc]
    constructor
    · omega
    · have := hneg i
      omega
  · intro e _ f _ hef
    apply Subtype.ext
    ext i
    exact congrFun hef i

/-- For fixed total degree and finitely many coordinates, there are only finitely many homogeneous
Laurent exponents that are nonnegative in every coordinate. -/
theorem LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_empty
    [Fintype σ] (d : ℤ) :
    {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d |
      e.liftedNegativeSupport = ∅}.Finite := by
  classical
  apply Set.Finite.of_finite_image
      (f := fun e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d => (e.1 : σ → ℤ))
  · apply (Set.Finite.pi' fun _ => Set.finite_Icc 0 d).subset
    rintro f ⟨e, he, rfl⟩
    intro i
    have hnonneg (j : σ) : 0 ≤ e.1 j := by
      by_contra hj
      have hj' : ULift.up j ∈ e.liftedNegativeSupport := by
        simpa [LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.liftedNegativeSupport] using
          (lt_of_not_ge hj)
      rw [he] at hj'
      exact hj'
    have hrest : 0 ≤ ∑ j ∈ Finset.univ.erase i, e.1 j := by
      apply Finset.sum_nonneg
      intro j _
      exact hnonneg j
    have hsum : ∑ j, e.1 j = d := by
      rw [← Finsupp.degree_eq_sum]
      exact e.2
    have hi : i ∈ (Finset.univ : Finset σ) := Finset.mem_univ i
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset σ)
      (fun j => e.1 j) hi
    simp only [Set.mem_Icc]
    constructor
    · exact hnonneg i
    · omega
  · intro e _ f _ hef
    apply Subtype.ext
    ext i
    exact congrFun hef i

/-- A homogeneous Laurent exponent of nonnegative degree has a coordinate outside its negative
support. -/
theorem LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.exists_not_mem_liftedNegativeSupport_of_nonneg
    {d : ℤ} (e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) (j : σ) (hd : 0 ≤ d) :
    ∃ i : ULift.{u} σ, i ∉ e.liftedNegativeSupport := by
  by_contra h
  have hall : ∀ i : σ, e.1 i < 0 := by
    intro i
    by_contra hi
    apply h
    exact ⟨ULift.up i, hi⟩
  have hdegree : Finsupp.degree e.1 < 0 := by
    rw [Finsupp.degree_apply]
    apply Finset.sum_neg
    · intro i _
      exact hall i
    · exact ⟨j, Finsupp.mem_support_iff.mpr (ne_of_lt (hall j))⟩
  rw [e.2] at hdegree
  exact (not_lt_of_ge hd) hdegree

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective
