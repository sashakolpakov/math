/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.AlgebraicGeometry.Noetherian
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentCocycleDecomposition
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupportAlternating
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights

/-! # Twist Cech Higher -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechHigher.MvPolynomial

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

local instance twistCechHigherDecidableEq : DecidableEq σ := Classical.decEq σ

/-- Assemble a full-negative cocycle into the homogeneous Laurent ordered Cech term. -/
noncomputable def coordinateHomogeneousLaurentFullNegativeCyclesAssembly
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ) :
    LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles
        (R := R) (σ := σ) d n →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n :=
  (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeAssembly
    (R := R) (σ := σ) d n).comp
      (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles
        (R := R) (σ := σ) d n).subtype

/-- The assembly of a full-negative cocycle is a cocycle in the homogeneous Laurent ordered Cech
complex. -/
theorem coordinateHomogeneousLaurentFullNegativeCyclesAssembly_differential
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles
      (R := R) (σ := σ) d n) :
    (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d n).hom
        (coordinateHomogeneousLaurentFullNegativeCyclesAssembly
          (R := R) (σ := σ) d n s) = 0 := by
  change
    (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d n).hom
        (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeAssembly
          (R := R) (σ := σ) d n s.1) = 0
  rw [LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeAssembly_differential]
  have hs : LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeDifferential
      (R := R) (σ := σ) d n s.1 = 0 := by
    simpa [LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles] using s.2
  rw [hs, map_zero]

/-- The exceptional full-negative cycles, lifted to the cycle object of the homogeneous Laurent
ordered Cech complex. -/
noncomputable def coordinateHomogeneousLaurentFullNegativeCyclesToCycles
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles
          (R := R) (σ := σ) d n) ⟶
      (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).cycles n :=
  by
    let k : ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles
          (R := R) (σ := σ) d n) ⟶
        (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
          (R := R) j d).X n :=
      ModuleCat.ofHom
        (coordinateHomogeneousLaurentFullNegativeCyclesAssembly
          (R := R) (σ := σ) d n)
    refine (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).liftCycles (i := n) k (n + 1) (by simp) ?_
    rw [TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact coordinateHomogeneousLaurentFullNegativeCyclesAssembly_differential
      (R := R) (σ := σ) d n s

/-- The exceptional-cycle lift followed by the cycle inclusion is the original assembly. -/
theorem coordinateHomogeneousLaurentFullNegativeCyclesToCycles_i
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    coordinateHomogeneousLaurentFullNegativeCyclesToCycles
        (R := R) j d n ≫
      (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).iCycles n =
    (ModuleCat.ofHom
        (coordinateHomogeneousLaurentFullNegativeCyclesAssembly
          (R := R) (σ := σ) d n) :
      ModuleCat.of
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles
            (R := R) (σ := σ) d n) ⟶
        (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
          (R := R) j d).X n) := by
  let k : ModuleCat.of
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles
        (R := R) (σ := σ) d n) ⟶
      (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).X n :=
    ModuleCat.ofHom
      (coordinateHomogeneousLaurentFullNegativeCyclesAssembly
        (R := R) (σ := σ) d n)
  have hk : k ≫ (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).d n (n + 1) = 0 := by
    rw [TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact coordinateHomogeneousLaurentFullNegativeCyclesAssembly_differential
      (R := R) (σ := σ) d n s
  simpa only [coordinateHomogeneousLaurentFullNegativeCyclesToCycles, k] using
    (HomologicalComplex.liftCycles_i
      (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d)
      k (n + 1) (by simp) hk)

/-- The homology class represented by an exceptional full-negative cycle. -/
noncomputable def coordinateHomogeneousLaurentFullNegativeCyclesToHomology
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles
          (R := R) (σ := σ) d n) ⟶
      (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).homology n :=
  coordinateHomogeneousLaurentFullNegativeCyclesToCycles
      (R := R) j d n ≫
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).homologyπ n

/-- Cycles whose difference is a boundary have the same class in homogeneous Laurent ordered-Cech
homology. -/
theorem coordinateHomogeneousLaurentOrderedCech_homologyπ_eq_of_sub_eq_boundary
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ)
    (z w : (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).cycles (n + 1))
    (t : LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n)
    (h : (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
          (R := R) j d).iCycles (n + 1) z -
        (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
          (R := R) j d).iCycles (n + 1) w =
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n).hom t) :
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).homologyπ (n + 1) z =
      (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).homologyπ (n + 1) w := by
  let K := TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
    (R := R) j d
  change K.homologyπ (n + 1) z = K.homologyπ (n + 1) w
  have hcycles : z - w = K.toCycles n (n + 1) t := by
    apply (ModuleCat.mono_iff_injective (K.iCycles (n + 1))).mp inferInstance
    have hsub :
        K.iCycles (n + 1) z - K.iCycles (n + 1) w =
          (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
            (R := R) (σ := σ) d n).hom t := by
      simpa only [K] using h
    have hd :
        (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
            (R := R) (σ := σ) d n).hom t =
          K.d n (n + 1) t := by
      have hd' := congrArg (fun f => f t)
        (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d
          (R := R) j d n)
      exact hd'.symm
    have hi :
        K.d n (n + 1) t =
          K.iCycles (n + 1) (K.toCycles n (n + 1) t) := by
      have hi' := congrArg (fun f => f t) (K.toCycles_i n (n + 1))
      change K.iCycles (n + 1) (K.toCycles n (n + 1) t) =
        K.d n (n + 1) t at hi'
      exact hi'.symm
    rw [map_sub]
    exact hsub.trans (hd.trans hi)
  have hboundary := congrArg (fun f => f t)
    (K.toCycles_comp_homologyπ n (n + 1))
  change K.homologyπ (n + 1) (K.toCycles n (n + 1) t) = 0 at hboundary
  apply sub_eq_zero.mp
  rw [← map_sub, hcycles]
  exact hboundary

/-- Project a cycle in the homogeneous Laurent complex to its full-negative weight cycle. -/
noncomputable def coordinateHomogeneousLaurentCyclesToFullNegativeCycles
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).cycles n ⟶
      ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles
          (R := R) (σ := σ) d n) :=
  by
    let p : (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).cycles n ⟶ ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain
          (R := R) (σ := σ) d n) :=
      (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
          (R := R) j d).iCycles n ≫
        ModuleCat.ofHom
          (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
            (R := R) d n)
    have hprojection :
        (ModuleCat.ofHom
            (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
              (R := R) d n) :
          LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
              (R := R) (σ := σ) d n ⟶
            ModuleCat.of
              Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
              (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain
                (R := R) (σ := σ) d n)) ≫
          ModuleCat.ofHom
            (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeDifferential
              (R := R) (σ := σ) d n) =
        LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
            (R := R) (σ := σ) d n ≫
          ModuleCat.ofHom
            (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
              (R := R) d (n + 1)) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      exact LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection_differential
        (R := R) (σ := σ) d n s
    have hp : p ≫ ModuleCat.ofHom
        (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeDifferential
          (R := R) (σ := σ) d n) = 0 := by
      dsimp only [p]
      calc
        ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
              (R := R) j d).iCycles n ≫
            ModuleCat.ofHom
              (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
                (R := R) d n)) ≫
            ModuleCat.ofHom
              (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeDifferential
                (R := R) (σ := σ) d n) =
          (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
              (R := R) j d).iCycles n ≫
            (ModuleCat.ofHom
                (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
                  (R := R) d n) ≫
              ModuleCat.ofHom
                (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeDifferential
                  (R := R) (σ := σ) d n)) := Category.assoc _ _ _
        _ = (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
              (R := R) j d).iCycles n ≫
            (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
                (R := R) (σ := σ) d n ≫
              ModuleCat.ofHom
                (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
                  (R := R) d (n + 1))) :=
          congrArg (fun q =>
            (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
              (R := R) j d).iCycles n ≫ q) hprojection
        _ = ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
              (R := R) j d).iCycles n ≫
            LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
              (R := R) (σ := σ) d n) ≫
              ModuleCat.ofHom
                (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
                  (R := R) d (n + 1)) := (Category.assoc _ _ _).symm
        _ = ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
              (R := R) j d).iCycles n ≫
            (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
              (R := R) j d).d n (n + 1)) ≫
              ModuleCat.ofHom
                (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
                  (R := R) d (n + 1)) :=
          congrArg (fun q =>
            ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
                (R := R) j d).iCycles n ≫ q) ≫
              ModuleCat.ofHom
                (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
                  (R := R) d (n + 1)))
            (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d
              (R := R) j d n).symm
        _ = 0 := calc
          _ = 0 ≫ ModuleCat.ofHom
              (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
                (R := R) d (n + 1)) :=
            congrArg (fun q => q ≫ ModuleCat.ofHom
              (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
                (R := R) d (n + 1)))
              ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
                (R := R) j d).iCycles_d n (n + 1))
          _ = 0 := Limits.zero_comp
    refine ModuleCat.ofHom (p.hom.codRestrict
      (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles
        (R := R) (σ := σ) d n) (fun s => ?_))
    rw [LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles, LinearMap.mem_ker]
    change LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeDifferential
      (R := R) (σ := σ) d n (p.hom s) = 0
    exact congrArg (fun f => f s) hp

/-- Projecting an ambient cycle and then including the full-negative cycle recovers the
componentwise projection of that ambient cycle. -/
theorem coordinateHomogeneousLaurentCyclesToFullNegativeCycles_i
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    coordinateHomogeneousLaurentCyclesToFullNegativeCycles
        (R := R) j d n ≫
        ModuleCat.ofHom
          (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles
            (R := R) (σ := σ) d n).subtype =
      (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
          (R := R) j d).iCycles n ≫
        ModuleCat.ofHom
          (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
            (R := R) d n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  rfl

private theorem iCycles_coordinateDifferential_eq_zero
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ)
    (z : (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).cycles n) :
    (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d n).hom
        ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
          (R := R) j d).iCycles n z) = 0 := by
  let K := TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
    (R := R) j d
  have hz := congrArg (fun f => f z) (K.iCycles_d n (n + 1))
  change K.d n (n + 1) (K.iCycles n z) = 0 at hz
  have hd := congrArg (fun f => f (K.iCycles n z))
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d
      (R := R) j d n)
  exact hd.symm.trans hz

/-- Project a degree-zero homogeneous Laurent cycle onto all weight components with empty negative
support. -/
noncomputable def coordinateHomogeneousLaurentCyclesZeroToNonnegativeCochain
    [LinearOrder σ] (j : σ) (d : ℤ) :
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).cycles 0 →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentNonnegativeCochain
        (R := R) (σ := σ) d :=
  (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentNonnegativeProjection
    (R := R) (σ := σ) d).comp
    ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).iCycles 0).hom

/-- A degree-zero homogeneous Laurent cycle is determined by its weight components with empty
negative support. -/
theorem coordinateHomogeneousLaurentCyclesZeroToNonnegativeCochain_injective
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] (j : σ) (d : ℤ) :
    Function.Injective
      (coordinateHomogeneousLaurentCyclesZeroToNonnegativeCochain
        (R := R) j d) := by
  classical
  intro z w hzw
  apply (ModuleCat.mono_iff_injective
    ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).iCycles 0)).mp inferInstance
  let z' : LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d 0 :=
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).iCycles 0 z
  let w' : LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d 0 :=
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).iCycles 0 w
  let x : LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d 0 := z' - w'
  have hz' :
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d 0).hom z' = 0 := by
    dsimp only [z']
    exact iCycles_coordinateDifferential_eq_zero (R := R) j d 0 z
  have hw' :
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d 0).hom w' = 0 := by
    dsimp only [w']
    exact iCycles_coordinateDifferential_eq_zero (R := R) j d 0 w
  have hxcycle :
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d 0).hom x = 0 := by
    change (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d 0).hom (z' - w') = 0
    rw [map_sub, hz', hw', sub_zero]
  have hcomponent (e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) :
      TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
          (R := R) d e 0 x = 0 := by
    by_cases he : e.liftedNegativeSupport = ∅
    · have heq := congrFun hzw ⟨e, he⟩
      change TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
          (R := R) d e 0 z' =
        TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
          (R := R) d e 0 w' at heq
      dsimp only [x]
      rw [map_sub, heq, sub_self]
    · apply OrderedCechSupportContraction.orderedCechSupportDifferential_zero_injective_of_nonempty
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.liftedNegativeSupport (Set.nonempty_iff_ne_empty.mpr he)
      rw [map_zero]
      rw [← TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_differential
        (R := R) (σ := σ) (d := d) (e := e) (n := 0)]
      rw [hxcycle, map_zero]
  have hx : x = 0 := by
    rw [← TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights_reconstruct d 0 x]
    simp only [hcomponent, map_zero, Finset.sum_const_zero]
  simpa only [x, z', w',
    TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_X] using sub_eq_zero.mp hx

/-- Degree-zero cycles of the homogeneous Laurent ordered Cech complex form a finite module over a
Noetherian coefficient ring. -/
theorem coordinateHomogeneousLaurentOrderedCechComplex_cycles_zero_module_finite
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    (j : σ) (d : ℤ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).cycles 0) := by
  let : IsNoetherianRing
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
    isNoetherianRing_of_ringEquiv R
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  let : Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentNonnegativeCochain
        (R := R) (σ := σ) d) :=
    LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentNonnegativeCochain.module_finite d
  exact Module.Finite.of_injective
    (coordinateHomogeneousLaurentCyclesZeroToNonnegativeCochain
      (R := R) j d)
    (coordinateHomogeneousLaurentCyclesZeroToNonnegativeCochain_injective
      (R := R) j d)

private theorem fullNegativeCyclesToCycles_projection
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ)
    (z : (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).cycles n) :
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).iCycles n
        ((coordinateHomogeneousLaurentFullNegativeCyclesToCycles
          (R := R) j d n).hom
          ((coordinateHomogeneousLaurentCyclesToFullNegativeCycles
            (R := R) j d n).hom z)) =
      LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeAssembly
        (R := R) (σ := σ) d n
        (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
          (R := R) d n
          ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
            (R := R) j d).iCycles n z)) := by
  let K := TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
    (R := R) j d
  let q := (coordinateHomogeneousLaurentCyclesToFullNegativeCycles
    (R := R) j d n).hom z
  have hqval :
      (q : LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain
        (R := R) (σ := σ) d n) =
      LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
        (R := R) d n (K.iCycles n z) := by
    have h := congrArg (fun f => f z)
      (coordinateHomogeneousLaurentCyclesToFullNegativeCycles_i
        (R := R) j d n)
    change
      ((coordinateHomogeneousLaurentCyclesToFullNegativeCycles
          (R := R) j d n).hom z :
        LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain
          (R := R) (σ := σ) d n) =
        LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
          (R := R) d n (K.iCycles n z) at h
    exact h
  have hiq := congrArg (fun f => f q)
    (coordinateHomogeneousLaurentFullNegativeCyclesToCycles_i
      (R := R) j d n)
  change
    K.iCycles n
        ((coordinateHomogeneousLaurentFullNegativeCyclesToCycles
          (R := R) j d n).hom q) =
      coordinateHomogeneousLaurentFullNegativeCyclesAssembly
        (R := R) (σ := σ) d n q at hiq
  have hcyclesAssembly :
      coordinateHomogeneousLaurentFullNegativeCyclesAssembly
          (R := R) (σ := σ) d n q =
        LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeAssembly
          (R := R) (σ := σ) d n q.1 := rfl
  have hqassembly := congrArg
    (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeAssembly
      (R := R) (σ := σ) d n) hqval
  exact hiq.trans (hcyclesAssembly.trans hqassembly)

/-- Every homogeneous Laurent cycle differs from the cycle assembled from its full-negative
projection by a boundary. -/
theorem exists_boundary_coordinateHomogeneousLaurentCycle_sub_fullNegativeCycle
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ)
    (z : (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).cycles (n + 1)) :
    ∃ t : LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n,
      (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
          (R := R) j d).iCycles (n + 1) z -
        (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
          (R := R) j d).iCycles (n + 1)
          ((coordinateHomogeneousLaurentFullNegativeCyclesToCycles
            (R := R) j d (n + 1)).hom
            ((coordinateHomogeneousLaurentCyclesToFullNegativeCycles
              (R := R) j d (n + 1)).hom z)) =
        (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) d n).hom t := by
  let K := TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
    (R := R) j d
  let s := K.iCycles (n + 1) z
  let q := (coordinateHomogeneousLaurentCyclesToFullNegativeCycles
    (R := R) j d (n + 1)).hom z
  have hs :
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d (n + 1)).hom s = 0 := by
    exact iCycles_coordinateDifferential_eq_zero
      (R := R) j d (n + 1) z
  obtain ⟨t, ht⟩ :=
    LaurentCocycleDecomposition.MvPolynomial.exists_boundary_add_fullNegativeWeights_eq_coordinateHomogeneousLaurentCocycle
      (R := R) (σ := σ) d n s hs
  have hiq :
      K.iCycles (n + 1)
          ((coordinateHomogeneousLaurentFullNegativeCyclesToCycles
            (R := R) j d (n + 1)).hom q) =
        LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeAssembly
          (R := R) (σ := σ) d (n + 1)
          (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
            (R := R) d (n + 1) s) := by
    exact fullNegativeCyclesToCycles_projection
      (R := R) j d (n + 1) z
  have hassembly := LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeAssembly_projection
    (R := R) (σ := σ) d (n + 1) s
  rw [← hassembly] at ht
  refine ⟨t, ?_⟩
  change
      K.iCycles (n + 1) z -
          K.iCycles (n + 1)
            ((coordinateHomogeneousLaurentFullNegativeCyclesToCycles
              (R := R) j d (n + 1)).hom q) =
        (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) d n).hom t
  rw [hiq]
  change s - _ = _
  exact (congrArg (fun x => x -
    LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeAssembly
      (R := R) (σ := σ) d (n + 1)
      (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection
        (R := R) d (n + 1) s)) ht.symm).trans
    (add_sub_cancel_right _ _)

/-- Full-negative cycles generate positive-degree homogeneous Laurent ordered-Cech homology. -/
theorem coordinateHomogeneousLaurentFullNegativeCyclesToHomology_surjective
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    Function.Surjective
      (coordinateHomogeneousLaurentFullNegativeCyclesToHomology
        (R := R) j d (n + 1)).hom := by
  let K := TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
    (R := R) j d
  intro x
  obtain ⟨z, hz⟩ :=
    (ModuleCat.epi_iff_surjective (K.homologyπ (n + 1))).mp inferInstance x
  let q := (coordinateHomogeneousLaurentCyclesToFullNegativeCycles
    (R := R) j d (n + 1)).hom z
  obtain ⟨t, hboundary⟩ :=
    exists_boundary_coordinateHomogeneousLaurentCycle_sub_fullNegativeCycle
      (R := R) j d n z
  have heq :=
    coordinateHomogeneousLaurentOrderedCech_homologyπ_eq_of_sub_eq_boundary
      (R := R) j d n z
      ((coordinateHomogeneousLaurentFullNegativeCyclesToCycles
        (R := R) j d (n + 1)).hom q) t hboundary
  refine ⟨q, ?_⟩
  change
    K.homologyπ (n + 1)
        ((coordinateHomogeneousLaurentFullNegativeCyclesToCycles
          (R := R) j d (n + 1)).hom q) = x
  exact heq.symm.trans hz

/-- Degree-zero homogeneous Laurent ordered-Cech homology is finite over a Noetherian coefficient
ring. -/
theorem coordinateHomogeneousLaurentOrderedCechComplex_homology_zero_module_finite
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    (j : σ) (d : ℤ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).homology 0) := by
  let K := TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
    (R := R) j d
  let : Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (K.cycles 0) :=
    coordinateHomogeneousLaurentOrderedCechComplex_cycles_zero_module_finite
      j d
  exact Module.Finite.of_surjective (K.homologyπ 0).hom
    ((ModuleCat.epi_iff_surjective (K.homologyπ 0)).mp inferInstance)

/-- Degree-zero homology of the explicit standard-coordinate ordered-Cech complex for a projective
twist is finite over a Noetherian coefficient ring. -/
theorem coordinateHyperplaneTwistOrderedBaseCechComplex_homology_zero_module_finite
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    (j : σ) (d : ℤ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplex
        (R := R) j d).homology 0) := by
  let : Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).homology 0) :=
    coordinateHomogeneousLaurentOrderedCechComplex_homology_zero_module_finite
      j d
  exact Module.Finite.equiv
    (HomologicalComplex.homologyMapIso
      (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplexIso
        (R := R) j d) 0).symm.toLinearEquiv

/-- Degree-zero homology of the native ordered-Cech complex for a coordinate-hyperplane twist is
finite over a Noetherian coefficient ring. -/
theorem coordinateHyperplaneTwist_orderedBaseCechComplex_homology_zero_module_finite
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    (j : σ) (d : ℤ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology 0) := by
  let : Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplex
        (R := R) j d).homology 0) :=
    coordinateHyperplaneTwistOrderedBaseCechComplex_homology_zero_module_finite
      j d
  exact Module.Finite.equiv
    (HomologicalComplex.homologyMapIso
      (TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso
        (R := R) j d) 0).symm.toLinearEquiv

/-- Positive-degree homogeneous Laurent ordered-Cech homology is finite over a Noetherian
coefficient ring. -/
theorem coordinateHomogeneousLaurentOrderedCechComplex_homology_module_finite
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    (j : σ) (d : ℤ) (n : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).homology (n + 1)) := by
  let : Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles
        (R := R) (σ := σ) d (n + 1)) :=
    LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles.module_finite d (n + 1)
  exact Module.Finite.of_surjective
    (coordinateHomogeneousLaurentFullNegativeCyclesToHomology
      (R := R) j d (n + 1)).hom
    (coordinateHomogeneousLaurentFullNegativeCyclesToHomology_surjective
      (R := R) j d n)

/-- Positive-degree homology of the explicit standard-coordinate ordered-Cech complex for a
projective twist is finite over a Noetherian coefficient ring. -/
theorem coordinateHyperplaneTwistOrderedBaseCechComplex_homology_module_finite
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    (j : σ) (d : ℤ) (n : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplex
        (R := R) j d).homology (n + 1)) := by
  let : Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).homology (n + 1)) :=
    coordinateHomogeneousLaurentOrderedCechComplex_homology_module_finite
      j d n
  exact Module.Finite.equiv
    (HomologicalComplex.homologyMapIso
      (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplexIso
        (R := R) j d) (n + 1)).symm.toLinearEquiv

/-- Positive-degree homology of the native ordered-Cech complex for a coordinate-hyperplane twist
is finite over a Noetherian coefficient ring. -/
theorem coordinateHyperplaneTwist_orderedBaseCechComplex_homology_module_finite
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    (j : σ) (d : ℤ) (n : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology (n + 1)) := by
  let : Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplex
        (R := R) j d).homology (n + 1)) :=
    coordinateHyperplaneTwistOrderedBaseCechComplex_homology_module_finite
      j d n
  exact Module.Finite.equiv
    (HomologicalComplex.homologyMapIso
      (TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso
        (R := R) j d) (n + 1)).symm.toLinearEquiv

/-- Every positive-degree cocycle in the homogeneous Laurent presentation of the ordered Cech
complex for a nonnegative projective twist is a boundary. -/
theorem exists_preimage_coordinateHomogeneousLaurentOrderedCechDifferential
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) (n : ℕ)
    (s : LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d (n + 1))
    (hs : (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d (n + 1)).hom s = 0) :
    ∃ t : LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n,
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n).hom t = s := by
  classical
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
  have hpreimage (e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) :
      ∃ t : OrderedCechSupportContraction.OrderedCechSupportCochain
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.liftedNegativeSupport n,
        OrderedCechSupportContraction.orderedCechSupportDifferential
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            e.liftedNegativeSupport n t =
          TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s := by
    obtain ⟨i, hi⟩ := e.exists_not_mem_liftedNegativeSupport_of_nonneg j hd
    exact OrderedCechSupportAlternating.exists_preimage_orderedCechSupportDifferential
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.liftedNegativeSupport i hi n
      (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent (R := R) d e (n + 1) s)
      (hcomponent_cycle e)
  choose t ht using hpreimage
  refine ⟨∑ e ∈ TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
    TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e n (t e), ?_⟩
  rw [map_sum]
  calc
    (∑ e ∈ TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
        (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) d n).hom
          (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e n (t e))) =
      ∑ e ∈ TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
        TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
          (OrderedCechSupportContraction.orderedCechSupportDifferential
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            e.liftedNegativeSupport n (t e)) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion_differential]
    _ = ∑ e ∈ TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
        TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
          (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [ht e]
    _ = s := TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights_reconstruct d (n + 1) s

/-- Every positive-degree cocycle in the explicit standard-coordinate ordered Cech complex for a
nonnegative projective twist is a boundary. -/
theorem exists_preimage_coordinateHyperplaneTwistOrderedBaseCechDifferential
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) (n : ℕ)
    (s : OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1))
    (hs : (TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechDifferential
      (R := R) (σ := σ) d (n + 1)).hom s = 0) :
    ∃ t : OrderedBaseCech.Scheme.Modules.orderedBaseCechObject
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n,
      (TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d n).hom t = s := by
  have hs_weight :
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d (n + 1)).hom
          ((LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
            (R := R) (σ := σ) d (n + 1)).hom.hom s) = 0 := by
    have h := congrArg (fun f => f.hom s)
      (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential_naturality
        (R := R) (σ := σ) d (n + 1))
    simpa [hs] using h
  obtain ⟨t, ht⟩ :=
    exists_preimage_coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) j d hd n
      ((LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d (n + 1)).hom.hom s) hs_weight
  refine ⟨(LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
    (R := R) (σ := σ) d n).inv.hom t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
      (R := R) (σ := σ) d (n + 1)).hom).1
  have h := congrArg (fun f => f.hom
      ((LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d n).inv.hom t))
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential_naturality
      (R := R) (σ := σ) d n)
  have h' :
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n).hom
          ((LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
            (R := R) (σ := σ) d n).hom.hom
            ((LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
              (R := R) (σ := σ) d n).inv.hom t)) =
        (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
          (R := R) (σ := σ) d (n + 1)).hom.hom
          ((TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechDifferential
            (R := R) (σ := σ) d n).hom
            ((LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso
              (R := R) (σ := σ) d n).inv.hom t)) := by
    simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] using h
  rw [← h']
  simpa using ht

/-- The explicit standard-coordinate ordered Cech complex for a nonnegative projective twist is
exact in every positive degree. -/
theorem coordinateHyperplaneTwistOrderedBaseCechComplex_exactAt_succ
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) (n : ℕ) :
    (TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplex
      (R := R) j d).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) ((n + 1) + 1)
    (by simp) (by simp)]
  have hsc : (ShortComplex.mk
      (TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d n)
      (TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d (n + 1))
      (TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechDifferential_comp
        (R := R) j d n)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro s hs
    exact exists_preimage_coordinateHyperplaneTwistOrderedBaseCechDifferential
      (R := R) (σ := σ) j d hd n s hs
  simpa only [HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor',
    TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplex_X,
    TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplex_d] using hsc

/-- The native ordered Cech complex of a nonnegative coordinate-hyperplane twist is exact in
every positive degree. -/
theorem coordinateHyperplaneTwist_orderedBaseCechComplex_exactAt_succ
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) (n : ℕ) :
    (OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).ExactAt (n + 1) := by
  exact (coordinateHyperplaneTwistOrderedBaseCechComplex_exactAt_succ
    (R := R) (σ := σ) j d hd n).of_iso
      (TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso
        (R := R) j d).symm

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechHigher.MvPolynomial
