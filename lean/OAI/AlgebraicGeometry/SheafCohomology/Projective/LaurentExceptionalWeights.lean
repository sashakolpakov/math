/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.AlgebraicGeometry.Noetherian
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeightAssembly
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupportAlternating

/-! # Laurent Exceptional Weights -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial

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

/-- The finite product of degree-zero support cochains indexed by homogeneous Laurent exponents
that are nonnegative in every coordinate. -/
abbrev coordinateHomogeneousLaurentNonnegativeCochain
    [LinearOrder σ] (d : ℤ) :=
  (e : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (∅ : Set (ULift.{u} σ))}) →
    OrderedCechSupportContraction.OrderedCechSupportCochain
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.1.liftedNegativeSupport 0

/-- Nonnegative homogeneous Laurent degree-zero cochains form a finite module over a Noetherian
affine coefficient ring. -/
theorem coordinateHomogeneousLaurentNonnegativeCochain.module_finite
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R] (d : ℤ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (coordinateHomogeneousLaurentNonnegativeCochain
        (R := R) (σ := σ) d) := by
  let : IsNoetherianRing
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
    isNoetherianRing_of_ringEquiv R
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  let : Finite {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (∅ : Set (ULift.{u} σ))} :=
    (LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_empty
      (σ := σ) d).to_subtype
  let (e : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (∅ : Set (ULift.{u} σ))}) :
      Module.Finite
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (OrderedCechSupportContraction.OrderedCechSupportCochain
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.1.liftedNegativeSupport 0) :=
    OrderedCechSupportContraction.OrderedCechSupportCochain.module_finite _ _ _
  infer_instance

/-- The finite product of support cochains indexed by the homogeneous Laurent exponents that are
negative in every coordinate. -/
abbrev coordinateHomogeneousLaurentFullNegativeCochain
    [LinearOrder σ] (d : ℤ) (n : ℕ) :=
  (e : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))}) →
    OrderedCechSupportContraction.OrderedCechSupportCochain
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.1.liftedNegativeSupport n

/-- Full-negative homogeneous Laurent cochains form a finite module over a Noetherian affine
coefficient ring. -/
theorem coordinateHomogeneousLaurentFullNegativeCochain.module_finite
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R] (d : ℤ) (n : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (coordinateHomogeneousLaurentFullNegativeCochain
        (R := R) (σ := σ) d n) := by
  let : IsNoetherianRing
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
    isNoetherianRing_of_ringEquiv R
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  let : Finite {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} :=
    (LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_univ
      (σ := σ) d).to_subtype
  let (e : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))}) :
      Module.Finite
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (OrderedCechSupportContraction.OrderedCechSupportCochain
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.1.liftedNegativeSupport n) :=
    OrderedCechSupportContraction.OrderedCechSupportCochain.module_finite _ _ _
  infer_instance

/-- Assemble the finitely many full-negative homogeneous Laurent weights into the ordered Cech
term. -/
noncomputable def coordinateHomogeneousLaurentFullNegativeAssembly
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ) :
    coordinateHomogeneousLaurentFullNegativeCochain
        (R := R) (σ := σ) d n →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n := by
  classical
  letI : Fintype {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} :=
    (LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_univ
      (σ := σ) d).fintype
  exact LinearMap.lsum
    Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
    (fun e : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
        e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} =>
      OrderedCechSupportContraction.OrderedCechSupportCochain
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        e.1.liftedNegativeSupport n)
    Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
    (fun e => TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion
      (R := R) d e.1 n)

/-- Full-negative assembly is the finite sum of the fixed-weight inclusions. -/
theorem coordinateHomogeneousLaurentFullNegativeAssembly_apply
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : coordinateHomogeneousLaurentFullNegativeCochain
      (R := R) (σ := σ) d n) :
    letI : Fintype {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} :=
    (LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_univ
      (σ := σ) d).fintype
    coordinateHomogeneousLaurentFullNegativeAssembly
        (R := R) (σ := σ) d n s =
      ∑ e : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
          e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))},
        TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion
          (R := R) d e.1 n (s e) := by
  classical
  simp [coordinateHomogeneousLaurentFullNegativeAssembly, LinearMap.lsum_apply]

/-- The componentwise ordered support differential on full-negative homogeneous Laurent
cochains. -/
noncomputable def coordinateHomogeneousLaurentFullNegativeDifferential
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    coordinateHomogeneousLaurentFullNegativeCochain
        (R := R) (σ := σ) d n →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      coordinateHomogeneousLaurentFullNegativeCochain
        (R := R) (σ := σ) d (n + 1) :=
  LinearMap.pi fun e =>
    (OrderedCechSupportContraction.orderedCechSupportDifferential
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.1.liftedNegativeSupport n).comp (LinearMap.proj e)

@[simp]
theorem coordinateHomogeneousLaurentFullNegativeDifferential_apply
    [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : coordinateHomogeneousLaurentFullNegativeCochain
      (R := R) (σ := σ) d n)
    (e : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))}) :
    coordinateHomogeneousLaurentFullNegativeDifferential
        (R := R) d n s e =
      OrderedCechSupportContraction.orderedCechSupportDifferential
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        e.1.liftedNegativeSupport n (s e) := rfl

/-- Full-negative assembly commutes with the homogeneous Laurent ordered Cech differential. -/
theorem coordinateHomogeneousLaurentFullNegativeAssembly_differential
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : coordinateHomogeneousLaurentFullNegativeCochain
      (R := R) (σ := σ) d n) :
    (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d n).hom
        (coordinateHomogeneousLaurentFullNegativeAssembly
          (R := R) (σ := σ) d n s) =
      coordinateHomogeneousLaurentFullNegativeAssembly
        (R := R) (σ := σ) d (n + 1)
        (coordinateHomogeneousLaurentFullNegativeDifferential
          (R := R) d n s) := by
  classical
  let : Fintype {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} :=
    (LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_univ
      (σ := σ) d).fintype
  have hleft :
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n).hom
          (coordinateHomogeneousLaurentFullNegativeAssembly
            (R := R) (σ := σ) d n s) =
        ∑ e : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
            e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))},
          (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
            (R := R) (σ := σ) d n).hom
            (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion
              (R := R) d e.1 n (s e)) := by
    rw [coordinateHomogeneousLaurentFullNegativeAssembly_apply, map_sum]
  have hright :
      coordinateHomogeneousLaurentFullNegativeAssembly
          (R := R) (σ := σ) d (n + 1)
          (coordinateHomogeneousLaurentFullNegativeDifferential
            (R := R) d n s) =
        ∑ e : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
            e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))},
          TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion
            (R := R) d e.1 (n + 1)
            (coordinateHomogeneousLaurentFullNegativeDifferential
              (R := R) d n s e) := by
    rw [coordinateHomogeneousLaurentFullNegativeAssembly_apply]
  rw [hleft, hright]
  apply Finset.sum_congr rfl
  intro e _
  rw [TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion_differential
    (R := R) (σ := σ) (d := d) (e := e.1) (n := n),
    coordinateHomogeneousLaurentFullNegativeDifferential_apply
      (R := R) (σ := σ) (d := d) (n := n) (s := s) (e := e)]

/-- Project a degree-zero homogeneous Laurent ordered Cech cochain onto all nonnegative weight
components. -/
noncomputable def coordinateHomogeneousLaurentNonnegativeProjection
    [LinearOrder σ] (d : ℤ) :
    LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d 0 →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      coordinateHomogeneousLaurentNonnegativeCochain
        (R := R) (σ := σ) d :=
  LinearMap.pi fun e =>
    TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
      (R := R) (σ := σ) d e.1 0

/-- Project a homogeneous Laurent ordered Cech cochain onto all full-negative weight
components. -/
noncomputable def coordinateHomogeneousLaurentFullNegativeProjection
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      coordinateHomogeneousLaurentFullNegativeCochain
        (R := R) (σ := σ) d n :=
  LinearMap.pi fun e =>
    TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
      (R := R) d e.1 n

@[simp]
theorem coordinateHomogeneousLaurentFullNegativeProjection_apply
    [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n)
    (e : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))}) :
    coordinateHomogeneousLaurentFullNegativeProjection
        (R := R) d n s e =
      TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
        (R := R) d e.1 n s := rfl

/-- Projection onto the full-negative weights commutes with the ordered Cech differential. -/
theorem coordinateHomogeneousLaurentFullNegativeProjection_differential
    [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n) :
    coordinateHomogeneousLaurentFullNegativeDifferential
        (R := R) (σ := σ) d n
        (coordinateHomogeneousLaurentFullNegativeProjection
          (R := R) d n s) =
      coordinateHomogeneousLaurentFullNegativeProjection
        (R := R) d (n + 1)
        ((LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) d n).hom s) := by
  ext e
  rw [coordinateHomogeneousLaurentFullNegativeDifferential_apply,
    coordinateHomogeneousLaurentFullNegativeProjection_apply,
    coordinateHomogeneousLaurentFullNegativeProjection_apply,
    TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_differential]

/-- A Laurent weight outside the active support of a cochain has zero weight component. -/
theorem coordinateHomogeneousLaurentWeightComponent_eq_zero_of_not_mem_active
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n)
    (e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d)
    (he : e ∉ TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights d n s) :
    TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
      (R := R) d e n s = 0 := by
  apply Subtype.ext
  funext a
  by_cases hallowed : e.IsAllowedOn (fun k => (a.1 k).down)
  · rw [TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_apply_of_allowed
      (h := hallowed)]
    by_contra hcoefficient
    exact he ((TwistCechWeightAssembly.MvPolynomial.mem_coordinateHomogeneousLaurentActiveWeights_iff
      d n s e).2 ⟨a, hallowed, hcoefficient⟩)
  · rw [TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_apply_of_not_allowed
      (h := hallowed)]
    rfl

/-- Assembling all full-negative components is the finite sum over the active full-negative
weights. -/
theorem coordinateHomogeneousLaurentFullNegativeAssembly_projection
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n) :
    coordinateHomogeneousLaurentFullNegativeAssembly
        (R := R) (σ := σ) d n
        (coordinateHomogeneousLaurentFullNegativeProjection
          (R := R) d n s) =
      ∑ e ∈ (TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights d n s).filter
          fun e => e.liftedNegativeSupport =
            (Set.univ : Set (ULift.{u} σ)),
        TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion
          (R := R) d e n
          (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
            (R := R) d e n s) := by
  classical
  let Full : Set (LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d) :=
    {e | e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))}
  let hE : Full.Finite :=
    LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_univ
      (σ := σ) d
  let E := hE.toFinset
  let eEquiv := hE.subtypeEquivToFinset
  let term : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d →
      LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n := fun e =>
    TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightInclusion
      (R := R) d e n
      (TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent
        (R := R) d e n s)
  let : Fintype Full := hE.fintype
  rw [coordinateHomogeneousLaurentFullNegativeAssembly_apply]
  change
    (∑ e : Full, term e.1) =
    ∑ e ∈ (TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights d n s).filter
        fun e => e.liftedNegativeSupport =
          (Set.univ : Set (ULift.{u} σ)), term e
  have hsubset :
      (TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights d n s).filter
          (fun e => e.liftedNegativeSupport =
            (Set.univ : Set (ULift.{u} σ))) ⊆ E := by
    intro e he
    apply hE.mem_toFinset.mpr
    simpa only [Full, Set.mem_ofPred_eq] using (Finset.mem_filter.mp he).2
  have hzero : ∀ e ∈ E,
      e ∉ (TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights d n s).filter
        (fun e => e.liftedNegativeSupport =
          (Set.univ : Set (ULift.{u} σ))) → term e = 0 := by
    intro e heE he
    have hfull : e.liftedNegativeSupport =
        (Set.univ : Set (ULift.{u} σ)) := by
      simpa only [Full, Set.mem_ofPred_eq] using hE.mem_toFinset.mp heE
    have hinactive : e ∉ TwistCechWeightAssembly.MvPolynomial.coordinateHomogeneousLaurentActiveWeights d n s := by
      intro hactive
      exact he (Finset.mem_filter.mpr ⟨hactive, hfull⟩)
    dsimp only [term]
    rw [coordinateHomogeneousLaurentWeightComponent_eq_zero_of_not_mem_active
      (R := R) (σ := σ) d n s e hinactive, map_zero]
  calc
    _ = ∑ e : {e // e ∈ E}, term e.1 := by
      exact Fintype.sum_equiv eEquiv
        (fun e : Full => term e.1)
        (fun e : {e // e ∈ E} => term e.1) (fun _ => rfl)
    _ = ∑ e ∈ E, term e := by
      rw [Finset.univ_eq_attach E]
      exact Finset.sum_attach E term
    _ = _ := (Finset.sum_subset hsubset hzero).symm

/-- The full-negative cocycles in one degree of the homogeneous Laurent ordered Cech
presentation. -/
def coordinateHomogeneousLaurentFullNegativeCycles
    [LinearOrder σ] (d : ℤ) (n : ℕ) :=
  LinearMap.ker
    (coordinateHomogeneousLaurentFullNegativeDifferential
      (R := R) (σ := σ) d n)

/-- Full-negative homogeneous Laurent cycles form a finite module over a Noetherian affine
coefficient ring. -/
theorem coordinateHomogeneousLaurentFullNegativeCycles.module_finite
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R] (d : ℤ) (n : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (coordinateHomogeneousLaurentFullNegativeCycles
        (R := R) (σ := σ) d n) := by
  let : IsNoetherianRing
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
    isNoetherianRing_of_ringEquiv R
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  let : Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (coordinateHomogeneousLaurentFullNegativeCochain
        (R := R) (σ := σ) d n) :=
    coordinateHomogeneousLaurentFullNegativeCochain.module_finite d n
  have hsource : IsNoetherian
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (coordinateHomogeneousLaurentFullNegativeCochain
        (R := R) (σ := σ) d n) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  let : IsNoetherian
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (coordinateHomogeneousLaurentFullNegativeCycles
        (R := R) (σ := σ) d n) :=
    isNoetherian_of_submodule_of_noetherian _ _ _ hsource
  infer_instance

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentExceptionalWeights.MvPolynomial
