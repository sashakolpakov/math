/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionHomotopyDegrees
import Mathlib.Algebra.Homology.Homotopy

/-! # Alternating Null Homotopy -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AlternatingNullHomotopy

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

noncomputable def coefficientCechAlternatingHomotopyComponent
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (i j : ℕ) (h : (ComplexShape.up ℕ).Rel j i) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X i ⟶
      (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X j := by
  change j + 1 = i at h
  subst i
  exact CechTuple.SectionHomotopy.coefficientCechAlternatingHomotopyF coefficientMap M U j

noncomputable def coefficientCechAlternatingNullHomotopicMap
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U ⟶ Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U :=
  Homotopy.nullHomotopicMap' fun i j h =>
    coefficientCechAlternatingHomotopyComponent coefficientMap M U i j h

theorem coefficientCechAlternatingNullHomotopicMap_f_zero
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    (coefficientCechAlternatingNullHomotopicMap coefficientMap M U).f 0 =
      (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d 0 1 ≫
        CechTuple.SectionHomotopy.coefficientCechAlternatingHomotopyF coefficientMap M U 0 := by
  let h01 : (ComplexShape.up ℕ).Rel 0 1 :=
    ComplexShape.up_mk 0 1 rfl
  rw [coefficientCechAlternatingNullHomotopicMap,
    Homotopy.nullHomotopicMap'_f_of_not_rel_right h01]
  · rfl
  · intro l hl
    change l + 1 = 0 at hl
    omega

theorem coefficientCechAlternatingNullHomotopicMap_f_succ
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (coefficientCechAlternatingNullHomotopicMap coefficientMap M U).f (n + 1) =
      (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d (n + 1) (n + 2) ≫
          CechTuple.SectionHomotopy.coefficientCechAlternatingHomotopyF coefficientMap M U (n + 1) +
        CechTuple.SectionHomotopy.coefficientCechAlternatingHomotopyF coefficientMap M U n ≫
          (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) := by
  let hn : (ComplexShape.up ℕ).Rel n (n + 1) :=
    ComplexShape.up_mk n (n + 1) rfl
  let hn' : (ComplexShape.up ℕ).Rel (n + 1) (n + 2) :=
    ComplexShape.up_mk (n + 1) (n + 2) rfl
  rw [coefficientCechAlternatingNullHomotopicMap,
    Homotopy.nullHomotopicMap'_f hn hn']
  rfl

theorem coefficientCechAlternatingNullHomotopicMap_eq
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    coefficientCechAlternatingNullHomotopicMap coefficientMap M U =
      OrderedCech.ComplexProjection.coefficientCechToOrdered coefficientMap M U ≫
          CoefficientCech.AlternatingMap.orderedToCoefficientCechAlternating coefficientMap M U -
        𝟙 (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U) := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
      rw [coefficientCechAlternatingNullHomotopicMap_f_zero]
      exact CechTuple.SectionHomotopyDegrees.coefficientCechAlternatingHomotopy_identity_zero coefficientMap M U
  | succ n =>
      rw [coefficientCechAlternatingNullHomotopicMap_f_succ]
      exact CechTuple.SectionHomotopyDegrees.coefficientCechAlternatingHomotopy_identity_succ coefficientMap M U n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AlternatingNullHomotopy
