/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FreeCech.TupleHomotopySupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AlternatingMap

/-! # Section Restrictions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionRestrictions

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- Inclusion of tuple intersections induced by inclusion of their index ranges. -/
theorem cechTupleIntersection_le_of_range_subset
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {n m : ℕ} (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : Set.range j ⊆ Set.range i) :
    (∏ᶜ fun k : Fin (n + 1) => U (i k)) ≤
      ∏ᶜ fun k : Fin (m + 1) => U (j k) := by
  classical
  choose q hq using fun k => h ⟨k, rfl⟩
  have hcomp : i ∘ q = j := funext hq
  have hmap :
      ((FormalCoproduct.mk _ U).mapPower q).f i = j := hcomp
  exact leOfHom
    (((FormalCoproduct.mk _ U).mapPower q).φ i ≫
      eqToHom (congrArg
        (fun t : Fin (m + 1) → ι => ∏ᶜ fun k => U (t k)) hmap))

/-- Restrict sections from a tuple intersection to a smaller tuple intersection. -/
noncomputable def coefficientCechTupleRestriction
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : Set.range j ⊆ Set.range i) :
    Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U m j ⟶ Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
  (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
    (homOfLE (cechTupleIntersection_le_of_range_subset U i j h)).op

/-- Restricting a tuple factor to itself is the identity. -/
theorem coefficientCechTupleRestriction_self
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n : ℕ}
    (i : Fin (n + 1) → ι) (h : Set.range i ⊆ Set.range i) :
    coefficientCechTupleRestriction coefficientMap M U i i h = 𝟙 _ := by
  let F := Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M
  let a := (homOfLE
    (cechTupleIntersection_le_of_range_subset U i i h)).op
  change F.map a = 𝟙 _
  calc
    F.map a = F.map (𝟙 _) :=
      congrArg F.map (Subsingleton.elim _ _)
    _ = 𝟙 _ := F.map_id _

/-- Tuple-factor restrictions compose along inclusions of index ranges. -/
theorem coefficientCechTupleRestriction_comp
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (k : Fin (l + 1) → ι) (hkj : Set.range k ⊆ Set.range j)
    (hji : Set.range j ⊆ Set.range i) :
    coefficientCechTupleRestriction coefficientMap M U j k hkj ≫
        coefficientCechTupleRestriction coefficientMap M U i j hji =
      coefficientCechTupleRestriction coefficientMap M U i k (hkj.trans hji) := by
  let F := Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M
  let a := (homOfLE
    (cechTupleIntersection_le_of_range_subset U j k hkj)).op
  let b := (homOfLE
    (cechTupleIntersection_le_of_range_subset U i j hji)).op
  let c := (homOfLE
    (cechTupleIntersection_le_of_range_subset U i k
      (hkj.trans hji))).op
  change F.map a ≫ F.map b = F.map c
  calc
    F.map a ≫ F.map b = F.map (a ≫ b) :=
      (F.map_comp a b).symm
    _ = F.map c := congrArg F.map (Subsingleton.elim _ _)

/-- Tuple restriction agrees with any map between the same two intersection opens. -/
theorem coefficientCechTupleRestriction_eq_map
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : Set.range j ⊆ Set.range i)
    (a : (∏ᶜ fun k : Fin (n + 1) => U (i k)) ⟶
      ∏ᶜ fun k : Fin (m + 1) => U (j k)) :
    coefficientCechTupleRestriction coefficientMap M U i j h =
      (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map a.op := by
  apply congrArg (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
  exact Subsingleton.elim _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionRestrictions
