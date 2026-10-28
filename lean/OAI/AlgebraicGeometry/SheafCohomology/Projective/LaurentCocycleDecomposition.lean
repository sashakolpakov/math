/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.AlgebraicGeometry.Noetherian
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentExceptionalWeights
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupportAlternating

/-! # Laurent Cocycle Decomposition -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentCocycleDecomposition.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-!
# Higher exactness for nonnegative projective twists

This file assembles the all-degree support contraction from
[Stacks Project, Lemma 30.8.1 (Tag 01XT)](https://stacks.math.columbia.edu/tag/01XT) weight by
weight in the homogeneous Laurent presentation of the ordered Cech complex.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance : DecidableEq σ := Classical.decEq σ

/-- Every positive-degree cocycle in the homogeneous Laurent presentation is a boundary modulo
the active weights that are negative in every coordinate. -/
theorem exists_boundary_add_fullNegativeWeights_eq_coordinateHomogeneousLaurentCocycle
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d (n + 1))
    (hs : (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d (n + 1)).hom s = 0) :
    ∃ t : LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n,
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) d n).hom t +
        (∑ e ∈ (TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights d (n + 1) s).filter
            fun e => e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ)),
          TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
            (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
              (R := R) d e (n + 1) s)) = s := by
  classical
  let A := TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights d (n + 1) s
  let N := A.filter fun e =>
    e.liftedNegativeSupport ≠ (Set.univ : Set (ULift.{u} σ))
  have hcomponent_cycle (e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) :
      OrderedCechSupportContraction.orderedCechSupportDifferential
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.liftedNegativeSupport (n + 1)
          (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s) = 0 := by
    rw [← TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_differential
      (R := R) (σ := σ) (d := d) (e := e) (n := n + 1), hs]
    exact map_zero
      (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent (R := R) d e (n + 2))
  have hpreimage (e : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d // e ∈ N}) :
      ∃ t : OrderedCechSupportContraction.OrderedCechSupportCochain
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.1.liftedNegativeSupport n,
        OrderedCechSupportContraction.orderedCechSupportDifferential
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            e.1.liftedNegativeSupport n t =
          TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
            (R := R) d e.1 (n + 1) s := by
    have he : e.1.liftedNegativeSupport ≠ (Set.univ : Set (ULift.{u} σ)) := by
      exact (Finset.mem_filter.mp e.2).2
    obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem _).mp he
    exact OrderedCechSupportAlternating.exists_preimage_orderedCechSupportDifferential
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.1.liftedNegativeSupport i hi n
      (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent (R := R) d e.1 (n + 1) s)
      (hcomponent_cycle e.1)
  choose t ht using hpreimage
  refine ⟨∑ e : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d // e ∈ N},
    TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e.1 n (t e), ?_⟩
  rw [map_sum]
  simp only [TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion_differential, ht]
  rw [Finset.univ_eq_attach N]
  have hsum :
      (∑ x ∈ N.attach,
        TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d x.1 (n + 1)
          (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
            (R := R) d x.1 (n + 1) s)) =
      ∑ e ∈ N,
        TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
          (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s) :=
    Finset.sum_attach N fun e =>
      TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
        (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
          (R := R) d e (n + 1) s)
  rw [hsum]
  change (∑ e ∈ N,
      TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
        (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
          (R := R) d e (n + 1) s)) +
      (∑ e ∈ A.filter (fun e =>
          e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))),
        TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
          (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s)) = s
  rw [show N = A.filter (fun e =>
      ¬e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))) by rfl]
  calc
    _ = (∑ e ∈ A.filter (fun e =>
          e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))),
          TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
            (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
              (R := R) d e (n + 1) s)) +
        (∑ e ∈ A.filter (fun e =>
          ¬e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))),
          TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
            (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
              (R := R) d e (n + 1) s)) := add_comm _ _
    _ = ∑ e ∈ A,
          TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
            (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
              (R := R) d e (n + 1) s) :=
      Finset.sum_filter_add_sum_filter_not A
        (fun e => e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))) _
    _ = s := TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights_reconstruct d (n + 1) s

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentCocycleDecomposition.MvPolynomial
