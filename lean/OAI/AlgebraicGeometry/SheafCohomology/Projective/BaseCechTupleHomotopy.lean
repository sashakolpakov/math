/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CechTupleAlternatingHomotopy

/-! # Base Cech Tuple Homotopy -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechTupleHomotopy

noncomputable section

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules

/-!
# Lifting tuple-chain homotopies to base-linear Cech cochains

This file turns a support-nonincreasing map of free tuple chains into a map between degrees of
the existing base-linear Cech complex. A tuple in the support of the image uses only indices from
the source tuple, so restriction of sections supplies the corresponding matrix coefficient.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Category
  _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite Set
  _root_.TopologicalSpace

universe u

namespace Scheme.Modules

open OAI.AlgebraicGeometry.SheafCohomology.Projective.CechTupleAlternatingHomotopy

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
noncomputable def baseCechTupleRestriction
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : Set.range j ⊆ Set.range i) :
    Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U m j ⟶ Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n i :=
  (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).map
    (homOfLE (cechTupleIntersection_le_of_range_subset U i j h)).op

/-- Restricting a tuple factor to itself is the identity. -/
theorem baseCechTupleRestriction_self
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n : ℕ}
    (i : Fin (n + 1) → ι) (h : Set.range i ⊆ Set.range i) :
    baseCechTupleRestriction π M U i i h = 𝟙 _ := by
  let F := Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M
  let a := (homOfLE
    (cechTupleIntersection_le_of_range_subset U i i h)).op
  change F.map a = 𝟙 _
  calc
    F.map a = F.map (𝟙 _) :=
      congrArg F.map (Subsingleton.elim _ _)
    _ = 𝟙 _ := F.map_id _

/-- Tuple-factor restrictions compose along inclusions of index ranges. -/
theorem baseCechTupleRestriction_comp
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (k : Fin (l + 1) → ι) (hkj : Set.range k ⊆ Set.range j)
    (hji : Set.range j ⊆ Set.range i) :
    baseCechTupleRestriction π M U j k hkj ≫
        baseCechTupleRestriction π M U i j hji =
      baseCechTupleRestriction π M U i k (hkj.trans hji) := by
  let F := Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M
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
theorem baseCechTupleRestriction_eq_map
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : Set.range j ⊆ Set.range i)
    (a : (∏ᶜ fun k : Fin (n + 1) => U (i k)) ⟶
      ∏ᶜ fun k : Fin (m + 1) => U (j k)) :
    baseCechTupleRestriction π M U i j h =
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).map a.op := by
  apply congrArg (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).map
  exact Subsingleton.elim _ _

/-- One basis entry in a tuple row, with unsupported entries discarded. -/
noncomputable def baseCechTupleRowBasis
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X m ⟶ Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n i := by
  classical
  let p : (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X m ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U m j :=
    Pi.π (fun q : Fin (m + 1) → ι =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U m q) j
  exact if h : Set.range j ⊆ Set.range i then
    p ≫ baseCechTupleRestriction π M U i j h
  else 0

theorem baseCechTupleRowBasis_of_subset
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : Set.range j ⊆ Set.range i) :
    baseCechTupleRowBasis π M U i j =
      Pi.π (fun q : Fin (m + 1) → ι =>
          Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U m q) j ≫
        baseCechTupleRestriction π M U i j h := by
  classical
  simp [baseCechTupleRowBasis, h]
  congr

theorem baseCechTupleRowBasis_of_not_subset
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : ¬Set.range j ⊆ Set.range i) :
    baseCechTupleRowBasis π M U i j = 0 := by
  classical
  simp [baseCechTupleRowBasis, h]

/-- A supported row-basis entry composes with tuple-factor restriction. -/
theorem baseCechTupleRowBasis_comp_restriction
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (k : Fin (l + 1) → ι) (hkj : Set.range k ⊆ Set.range j)
    (hji : Set.range j ⊆ Set.range i) :
    baseCechTupleRowBasis π M U j k ≫
        baseCechTupleRestriction π M U i j hji =
      baseCechTupleRowBasis π M U i k := by
  let p : (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X l ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U l k :=
    Pi.π (fun q : Fin (l + 1) → ι =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U l q) k
  calc
    baseCechTupleRowBasis π M U j k ≫
          baseCechTupleRestriction π M U i j hji =
        (p ≫ baseCechTupleRestriction π M U j k hkj) ≫
          baseCechTupleRestriction π M U i j hji := by
      rw [baseCechTupleRowBasis_of_subset π M U j k hkj]
      rfl
    _ = p ≫
        (baseCechTupleRestriction π M U j k hkj ≫
          baseCechTupleRestriction π M U i j hji) :=
      Category.assoc _ _ _
    _ = p ≫ baseCechTupleRestriction π M U i k
        (hkj.trans hji) := by
      rw [baseCechTupleRestriction_comp]
    _ = baseCechTupleRowBasis π M U i k := by
      rw [baseCechTupleRowBasis_of_subset
        π M U i k (hkj.trans hji)]
      rfl

/-- A tuple chain defines a finite row of restriction maps. -/
noncomputable def baseCechTupleRow
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) :
    CechTupleAlternatingHomotopy.CechTupleChain ι m →ₗ[ℤ]
      ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X m ⟶ Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n i) :=
  by
    exact Finsupp.lsum ℤ fun j =>
      LinearMap.toSpanSingleton ℤ _
        (baseCechTupleRowBasis π M U i j)

theorem baseCechTupleRow_single_of_subset
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) (a : ℤ)
    (h : Set.range j ⊆ Set.range i) :
    baseCechTupleRow π M U i (Finsupp.single j a) =
      a • (Pi.π (fun q : Fin (m + 1) → ι =>
          Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U m q) j ≫
        baseCechTupleRestriction π M U i j h) := by
  rw [baseCechTupleRow, Finsupp.lsum_single,
    LinearMap.toSpanSingleton_apply,
    baseCechTupleRowBasis_of_subset π M U i j h]
  rfl

theorem baseCechTupleRow_single_of_not_subset
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) (a : ℤ)
    (h : ¬Set.range j ⊆ Set.range i) :
    baseCechTupleRow π M U i (Finsupp.single j a) = 0 := by
  rw [baseCechTupleRow, Finsupp.lsum_single,
    LinearMap.toSpanSingleton_apply,
    baseCechTupleRowBasis_of_not_subset π M U i j h,
    smul_zero]

/-- Postcomposing a tuple row with restriction only changes its target tuple. -/
theorem baseCechTupleRow_comp_restriction
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (hji : Set.range j ⊆ Set.range i) (x : CechTupleAlternatingHomotopy.CechTupleChain ι l)
    (hx : CechTupleAlternatingHomotopy.CechTupleChain.SupportedBy x (Set.range j)) :
    baseCechTupleRow π M U j x ≫
        baseCechTupleRestriction π M U i j hji =
      baseCechTupleRow π M U i x := by
  classical
  rw [baseCechTupleRow, baseCechTupleRow,
    Finsupp.lsum_apply, Finsupp.lsum_apply]
  rw [Finsupp.sum, Finsupp.sum, sum_comp]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj := hx hk
  simp only [LinearMap.toSpanSingleton_apply]
  rw [zsmul_comp,
    baseCechTupleRowBasis_comp_restriction
      π M U i j k hkj hji]

/-- One row of the restriction matrix associated to a support-nonincreasing tuple-chain map. -/
noncomputable def baseCechTupleMapComponent
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f : CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι m)
    (_hf : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing f)
    (i : Fin (n + 1) → ι) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X m ⟶ Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n i :=
  baseCechTupleRow π M U i (f (Finsupp.single i 1))

/-- The cochain map between two degrees dual to a support-nonincreasing tuple-chain map. -/
noncomputable def baseCechTupleMapF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f : CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι m)
    (hf : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing f) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X m ⟶ (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n :=
  Pi.lift fun i => baseCechTupleMapComponent π M U f hf i

theorem baseCechTupleMapF_comp_π
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f : CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι m)
    (hf : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing f)
    (i : Fin (n + 1) → ι) :
    baseCechTupleMapF π M U f hf ≫
        Pi.π (fun q : Fin (n + 1) → ι =>
          Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n q) i =
      baseCechTupleMapComponent π M U f hf i :=
  Pi.lift_comp_π _ i

/-- The identity tuple-chain map does not enlarge support. -/
theorem cechTupleSupportNonincreasing_id
    {ι : Type u} {n : ℕ} :
    CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing
      (LinearMap.id : CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι n) := by
  intro i
  simpa using CechTupleAlternatingHomotopy.CechTupleChain.supportedBy_single i 1 Subset.rfl

/-- A sum of support-nonincreasing tuple-chain maps is support-nonincreasing. -/
theorem CechTupleSupportNonincreasing.add
    {ι : Type u} {n m : ℕ}
    {f g : CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι m}
    (hf : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing f)
    (hg : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing g) :
    CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing (f + g) := by
  intro i
  simpa using (hf i).add (hg i)

/-- A negated support-nonincreasing tuple-chain map is support-nonincreasing. -/
theorem CechTupleSupportNonincreasing.neg
    {ι : Type u} {n m : ℕ}
    {f : CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι m}
    (hf : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing f) :
    CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing (-f) := by
  intro i
  simpa using (hf i).smul (-1)

/-- A linear map out of a free integral module is the sum of its values on basis vectors. -/
theorem linearMap_apply_eq_finsupp_sum_single
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
theorem CechTupleSupportNonincreasing.map_supportedBy
    {ι : Type u} {n m : ℕ}
    {f : CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι m}
    (hf : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing f)
    (x : CechTupleAlternatingHomotopy.CechTupleChain ι n) (N : Set ι)
    (hx : CechTupleAlternatingHomotopy.CechTupleChain.SupportedBy x N) :
    CechTupleAlternatingHomotopy.CechTupleChain.SupportedBy (f x) N := by
  rw [linearMap_apply_eq_finsupp_sum_single]
  change CechTupleAlternatingHomotopy.CechTupleChain.SupportedBy
    (∑ i ∈ x.support,
      x i • f (Finsupp.single i 1)) N
  apply CechTupleAlternatingHomotopy.CechTupleChain.supportedBy_sum x.support _
  intro i hi
  exact CechTupleAlternatingHomotopy.CechTupleChain.SupportedBy.smul
    (CechTupleAlternatingHomotopy.CechTupleChain.SupportedBy.mono (hf i) (hx hi)) (x i)

/-- A composite of support-nonincreasing tuple-chain maps is support-nonincreasing. -/
theorem CechTupleSupportNonincreasing.comp
    {ι : Type u} {n m l : ℕ}
    {f : CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι m}
    {g : CechTupleAlternatingHomotopy.CechTupleChain ι m →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι l}
    (hg : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing g)
    (hf : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing f) :
    CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing (g.comp f) := by
  intro i
  exact CechTupleSupportNonincreasing.map_supportedBy
    hg (f (Finsupp.single i 1)) (Set.range i) (hf i)

/-- The tuple deletion boundary does not enlarge support. -/
theorem cechTupleBoundary_supportNonincreasing
    {ι : Type u} (n : ℕ) :
    CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing
      (CechTupleAlternatingHomotopy.cechTupleBoundary (ι := ι) n) := by
  intro i
  apply CechTupleAlternatingHomotopy.cechTupleBoundary_supportedBy
  exact CechTupleAlternatingHomotopy.CechTupleChain.supportedBy_single i 1 Subset.rfl

/-- The sorted-tuple projection does not enlarge support. -/
theorem cechTupleAlternatingProjection_supportNonincreasing
    {ι : Type u} [LinearOrder ι] (n : ℕ) :
    CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing
      (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection (ι := ι) n) := by
  intro i
  apply CechTupleAlternatingHomotopy.cechTupleAlternatingProjection_supportedBy
  exact CechTupleAlternatingHomotopy.CechTupleChain.supportedBy_single i 1 Subset.rfl

/-- The lower-degree term in the tuple homotopy does not enlarge support. -/
theorem cechTupleAlternatingHomotopyPrevious_supportNonincreasing
    {ι : Type u} [LinearOrder ι] (n : ℕ) :
    CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing
      (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopyPrevious (ι := ι) n) := by
  intro i
  cases n with
  | zero =>
      exact CechTupleAlternatingHomotopy.CechTupleChain.supportedBy_zero
  | succ n =>
      apply CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy_supportedBy
      apply CechTupleAlternatingHomotopy.cechTupleBoundary_supportedBy
      exact CechTupleAlternatingHomotopy.CechTupleChain.supportedBy_single i 1 Subset.rfl

/-- Extensionality for a map into one native base-Cech degree, using its concrete tuple factors. -/
theorem baseCechHom_ext
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    {A : ModuleCat.{u} Γ(S, (⊤ : S.Opens))}
    {f g : A ⟶ (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n}
    (h : ∀ i : Fin (n + 1) → ι,
      f ≫ Pi.π (fun q : Fin (n + 1) → ι =>
          Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n q) i =
        g ≫ Pi.π (fun q : Fin (n + 1) → ι =>
          Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n q) i) :
    f = g := by
  apply (cancel_mono (BaseCechProducts.Scheme.Modules.baseCechXIsoPi π M U n).hom).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have hi := h i
  have hcomp :
      (f ≫ (BaseCechProducts.Scheme.Modules.baseCechXIsoPi π M U n).hom) ≫
          ModuleCat.ofHom
            (LinearMap.proj i :
              (∀ q : Fin (n + 1) → ι,
                Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n q) →ₗ[
                  Γ(S, (⊤ : S.Opens))]
                Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n i) =
        (g ≫ (BaseCechProducts.Scheme.Modules.baseCechXIsoPi π M U n).hom) ≫
          ModuleCat.ofHom
            (LinearMap.proj i :
              (∀ q : Fin (n + 1) → ι,
                Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n q) →ₗ[
                  Γ(S, (⊤ : S.Opens))]
                Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n i) := by
    simpa only [Category.assoc, OrderedBaseCechAlternating.Scheme.Modules.baseCechXIsoPi_hom_comp_proj]
      using hi
  exact ConcreteCategory.congr_hom hcomp x

/-- The lift of the identity tuple-chain map is the identity on Cech cochains. -/
theorem baseCechTupleMapF_id
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    baseCechTupleMapF π M U
        (LinearMap.id :
          CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι n)
        cechTupleSupportNonincreasing_id =
      𝟙 (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n := by
  apply baseCechHom_ext π M U n
  intro i
  let p : (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n q) i
  calc
    baseCechTupleMapF π M U LinearMap.id
          cechTupleSupportNonincreasing_id ≫ p =
        baseCechTupleMapComponent π M U LinearMap.id
          cechTupleSupportNonincreasing_id i := by
      dsimp only [p]
      exact baseCechTupleMapF_comp_π π M U
        LinearMap.id cechTupleSupportNonincreasing_id i
    _ = p := by
      change baseCechTupleRow π M U i (Finsupp.single i 1) = p
      rw [baseCechTupleRow_single_of_subset
        π M U i i 1 Subset.rfl, one_zsmul,
        baseCechTupleRestriction_self]
      simp [p]
      rfl
    _ = 𝟙 (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n ≫ p :=
      (Category.id_comp p).symm

/-- The restriction lift is additive in the tuple-chain map. -/
theorem baseCechTupleMapF_add
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f g : CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι m)
    (hf : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing f)
    (hg : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing g) :
    baseCechTupleMapF π M U (f + g)
        (CechTupleSupportNonincreasing.add hf hg) =
      baseCechTupleMapF π M U f hf +
        baseCechTupleMapF π M U g hg := by
  apply baseCechHom_ext π M U n
  intro i
  let p : (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n q) i
  calc
    baseCechTupleMapF π M U (f + g)
          (CechTupleSupportNonincreasing.add hf hg) ≫ p =
        baseCechTupleMapComponent π M U (f + g)
          (CechTupleSupportNonincreasing.add hf hg) i := by
      dsimp only [p]
      exact baseCechTupleMapF_comp_π π M U
        (f + g) (CechTupleSupportNonincreasing.add hf hg) i
    _ = baseCechTupleMapComponent π M U f hf i +
        baseCechTupleMapComponent π M U g hg i := by
      change baseCechTupleRow π M U i
          ((f + g) (Finsupp.single i 1)) =
        baseCechTupleRow π M U i (f (Finsupp.single i 1)) +
          baseCechTupleRow π M U i (g (Finsupp.single i 1))
      simp
    _ = (baseCechTupleMapF π M U f hf ≫ p) +
        (baseCechTupleMapF π M U g hg ≫ p) := by
      dsimp only [p]
      rw [baseCechTupleMapF_comp_π,
        baseCechTupleMapF_comp_π]
    _ = (baseCechTupleMapF π M U f hf +
          baseCechTupleMapF π M U g hg) ≫ p :=
      by rw [add_comp]

/-- The restriction lift sends negation to negation. -/
theorem baseCechTupleMapF_neg
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f : CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι m)
    (hf : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing f) :
    baseCechTupleMapF π M U (-f)
        (CechTupleSupportNonincreasing.neg hf) =
      -baseCechTupleMapF π M U f hf := by
  apply baseCechHom_ext π M U n
  intro i
  let p : (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n q) i
  calc
    baseCechTupleMapF π M U (-f)
          (CechTupleSupportNonincreasing.neg hf) ≫ p =
        baseCechTupleMapComponent π M U (-f)
          (CechTupleSupportNonincreasing.neg hf) i := by
      dsimp only [p]
      exact baseCechTupleMapF_comp_π π M U (-f)
        (CechTupleSupportNonincreasing.neg hf) i
    _ = -baseCechTupleMapComponent π M U f hf i := by
      change baseCechTupleRow π M U i
          ((-f) (Finsupp.single i 1)) =
        -baseCechTupleRow π M U i (f (Finsupp.single i 1))
      simp
    _ = -(baseCechTupleMapF π M U f hf ≫ p) := by
      dsimp only [p]
      rw [baseCechTupleMapF_comp_π]
    _ = (-baseCechTupleMapF π M U f hf) ≫ p :=
      by rw [neg_comp]

/-- A lifted tuple map commutes with one supported tuple-row basis vector. -/
theorem baseCechTupleMapF_comp_row_single
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (g : CechTupleAlternatingHomotopy.CechTupleChain ι m →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι l)
    (hg : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing g)
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (hji : Set.range j ⊆ Set.range i) :
    baseCechTupleMapF π M U g hg ≫
        baseCechTupleRow π M U i (Finsupp.single j 1) =
      baseCechTupleRow π M U i
        (g (Finsupp.single j 1)) := by
  let p : (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X m ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U m j :=
    Pi.π (fun q : Fin (m + 1) → ι =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U m q) j
  have hrow :
      baseCechTupleRow π M U i (Finsupp.single j 1) =
        p ≫ baseCechTupleRestriction π M U i j hji := by
    rw [baseCechTupleRow_single_of_subset
      π M U i j 1 hji, one_zsmul]
    rfl
  have hproj :
      baseCechTupleMapF π M U g hg ≫ p =
        baseCechTupleMapComponent π M U g hg j := by
    dsimp only [p]
    exact baseCechTupleMapF_comp_π π M U g hg j
  calc
    baseCechTupleMapF π M U g hg ≫
          baseCechTupleRow π M U i (Finsupp.single j 1) =
        baseCechTupleMapF π M U g hg ≫
          (p ≫ baseCechTupleRestriction π M U i j hji) := by
      rw [hrow]
    _ = (baseCechTupleMapF π M U g hg ≫ p) ≫
        baseCechTupleRestriction π M U i j hji :=
      (Category.assoc _ _ _).symm
    _ = baseCechTupleMapComponent π M U g hg j ≫
        baseCechTupleRestriction π M U i j hji := by
      rw [hproj]
    _ = baseCechTupleRow π M U j
          (g (Finsupp.single j 1)) ≫
        baseCechTupleRestriction π M U i j hji := rfl
    _ = baseCechTupleRow π M U i
        (g (Finsupp.single j 1)) :=
      baseCechTupleRow_comp_restriction π M U i j hji
        (g (Finsupp.single j 1)) (hg j)

/-- A lifted tuple map commutes with every supported tuple row. -/
theorem baseCechTupleMapF_comp_row
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (g : CechTupleAlternatingHomotopy.CechTupleChain ι m →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι l)
    (hg : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing g)
    (i : Fin (n + 1) → ι) (x : CechTupleAlternatingHomotopy.CechTupleChain ι m)
    (hx : CechTupleAlternatingHomotopy.CechTupleChain.SupportedBy x (Set.range i)) :
    baseCechTupleMapF π M U g hg ≫
        baseCechTupleRow π M U i x =
      baseCechTupleRow π M U i (g x) := by
  classical
  have hsource := linearMap_apply_eq_finsupp_sum_single
    (baseCechTupleRow π M U i) x
  have htarget := linearMap_apply_eq_finsupp_sum_single
    ((baseCechTupleRow π M U i).comp g) x
  change baseCechTupleRow π M U i (g x) =
    x.sum (fun j a => a • baseCechTupleRow π M U i
      (g (Finsupp.single j 1))) at htarget
  rw [hsource, htarget]
  rw [Finsupp.sum, Finsupp.sum, comp_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [comp_zsmul,
    baseCechTupleMapF_comp_row_single π M U g hg i j (hx hj)]

/-- Lifting support-nonincreasing tuple maps reverses their composition. -/
theorem baseCechTupleMapF_comp
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (f : CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι m)
    (g : CechTupleAlternatingHomotopy.CechTupleChain ι m →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι l)
    (hf : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing f)
    (hg : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing g) :
    baseCechTupleMapF π M U (g.comp f)
        (CechTupleSupportNonincreasing.comp hg hf) =
      baseCechTupleMapF π M U g hg ≫
        baseCechTupleMapF π M U f hf := by
  apply baseCechHom_ext π M U n
  intro i
  let p : (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n q) i
  calc
    baseCechTupleMapF π M U (g.comp f)
          (CechTupleSupportNonincreasing.comp hg hf) ≫ p =
        baseCechTupleMapComponent π M U (g.comp f)
          (CechTupleSupportNonincreasing.comp hg hf) i := by
      dsimp only [p]
      exact baseCechTupleMapF_comp_π π M U (g.comp f)
        (CechTupleSupportNonincreasing.comp hg hf) i
    _ = baseCechTupleRow π M U i
        (g (f (Finsupp.single i 1))) := rfl
    _ = baseCechTupleMapF π M U g hg ≫
        baseCechTupleRow π M U i
          (f (Finsupp.single i 1)) :=
      (baseCechTupleMapF_comp_row π M U g hg i
        (f (Finsupp.single i 1)) (hf i)).symm
    _ = baseCechTupleMapF π M U g hg ≫
        baseCechTupleMapComponent π M U f hf i := rfl
    _ = baseCechTupleMapF π M U g hg ≫
        (baseCechTupleMapF π M U f hf ≫ p) := by
      dsimp only [p]
      rw [baseCechTupleMapF_comp_π]
    _ = (baseCechTupleMapF π M U g hg ≫
          baseCechTupleMapF π M U f hf) ≫ p :=
      (Category.assoc _ _ _).symm

/-- Deleting an entry does not introduce a new tuple index. -/
theorem cechTupleDelete_range_subset
    {ι : Type u} {n : ℕ} (i : Fin (n + 2) → ι)
    (k : Fin (n + 2)) :
    Set.range (CechTupleAlternatingHomotopy.cechTupleDelete i k) ⊆ Set.range i := by
  rintro x ⟨l, rfl⟩
  exact ⟨k.succAbove l, rfl⟩

/-- The restriction lift of the tuple boundary is the native base-Cech differential. -/
theorem baseCechTupleMapF_boundary
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    baseCechTupleMapF π M U
        (CechTupleAlternatingHomotopy.cechTupleBoundary (ι := ι) n)
        (cechTupleBoundary_supportNonincreasing n) =
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d n (n + 1) := by
  apply baseCechHom_ext π M U (n + 1)
  intro i
  let p : (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X (n + 1) ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U (n + 1) i :=
    Pi.π (fun q : Fin (n + 2) → ι =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U (n + 1) q) i
  let t : (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U (n + 1) i :=
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
      (Pi.π (fun q : Fin (n + 1) → ι =>
          Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n q)
            (CechTupleAlternatingHomotopy.cechTupleDelete i k) ≫
        (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op)
  have hcomponent :
      baseCechTupleMapComponent π M U
          (CechTupleAlternatingHomotopy.cechTupleBoundary (ι := ι) n)
          (cechTupleBoundary_supportNonincreasing n) i = t := by
    change baseCechTupleRow π M U i
        (CechTupleAlternatingHomotopy.cechTupleBoundary n (Finsupp.single i 1)) = t
    rw [CechTupleAlternatingHomotopy.cechTupleBoundary_single, one_smul]
    unfold CechTupleAlternatingHomotopy.cechTupleBoundaryBasis
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    let h := cechTupleDelete_range_subset i k
    rw [baseCechTupleRow_single_of_subset
      π M U i (CechTupleAlternatingHomotopy.cechTupleDelete i k)
        ((-1 : ℤ) ^ (k : ℕ)) h]
    congr 2
  calc
    baseCechTupleMapF π M U (CechTupleAlternatingHomotopy.cechTupleBoundary n)
          (cechTupleBoundary_supportNonincreasing n) ≫ p =
        baseCechTupleMapComponent π M U (CechTupleAlternatingHomotopy.cechTupleBoundary n)
          (cechTupleBoundary_supportNonincreasing n) i := by
      dsimp only [p]
      exact baseCechTupleMapF_comp_π π M U
        (CechTupleAlternatingHomotopy.cechTupleBoundary n)
          (cechTupleBoundary_supportNonincreasing n) i
    _ = t := hcomponent
    _ = (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d n (n + 1) ≫ p := by
      dsimp only [t, p]
      rw [OrderedBaseCechComparison.Scheme.Modules.baseCechComplex_d_comp_π]
      apply Finset.sum_congr rfl
      intro k _
      have hδ :
          (SimplexCategory.δ k).toOrderHom.toFun =
            k.succAbove := by
        change (⇑(ConcreteCategory.hom (SimplexCategory.δ k))) =
          k.succAbove
        exact SimplexCategory.coe_δ k
      rw [hδ]
      rfl

/-- The restriction lift of signed sorting is projection to ordered tuples followed by
alternating extension. -/
theorem baseCechTupleMapF_alternatingProjection
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    baseCechTupleMapF π M U
        (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection (ι := ι) n)
        (cechTupleAlternatingProjection_supportNonincreasing n) =
      OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF π M U n ≫
        OrderedBaseCechAlternating.Scheme.Modules.orderedToBaseCechAlternatingF π M U n := by
  apply baseCechHom_ext π M U n
  intro i
  let p : (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n q) i
  change baseCechTupleMapF π M U
      (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n)
        (cechTupleAlternatingProjection_supportNonincreasing n) ≫ p =
    (OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF π M U n ≫
      OrderedBaseCechAlternating.Scheme.Modules.orderedToBaseCechAlternatingF π M U n) ≫ p
  rw [Category.assoc]
  by_cases hi : Function.Injective i
  · let s := Tuple.sort i
    let j := i ∘ s
    have hj : StrictMono j :=
      (Tuple.monotone_sort i).strictMono_of_injective
        (hi.comp s.injective)
    let pj : (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n ⟶
        Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n j :=
      Pi.π (fun q : Fin (n + 1) → ι =>
        Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n q) j
    let q : OrderedBaseCech.Scheme.Modules.orderedBaseCechObject π M U n ⟶
        Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n j :=
      Pi.π (fun t : OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι n =>
        Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n t.1) ⟨j, hj⟩
    have hji : Set.range j ⊆ Set.range i := by
      rintro x ⟨k, rfl⟩
      exact ⟨s k, rfl⟩
    let r : Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n j ⟶
        Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n i :=
      baseCechTupleRestriction π M U i j hji
    have hr :
        r = (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower s).φ i).op := by
      dsimp only [r]
      exact baseCechTupleRestriction_eq_map π M U i j hji
        (((FormalCoproduct.mk _ U).mapPower s).φ i)
    have hleft :
        baseCechTupleMapF π M U
            (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n)
            (cechTupleAlternatingProjection_supportNonincreasing n) ≫ p =
          (Equiv.Perm.sign s : ℤ) • (pj ≫ r) := by
      calc
        baseCechTupleMapF π M U
              (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n)
              (cechTupleAlternatingProjection_supportNonincreasing n) ≫ p =
            baseCechTupleMapComponent π M U
              (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n)
              (cechTupleAlternatingProjection_supportNonincreasing n) i := by
          dsimp only [p]
          exact baseCechTupleMapF_comp_π π M U
            (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n)
              (cechTupleAlternatingProjection_supportNonincreasing n) i
        _ = baseCechTupleRow π M U i
              (CechTupleAlternatingHomotopy.cechTupleAlternatingProjectionBasis n i) := by
          change baseCechTupleRow π M U i
              (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n
                (Finsupp.single i 1)) =
            baseCechTupleRow π M U i
              (CechTupleAlternatingHomotopy.cechTupleAlternatingProjectionBasis n i)
          rw [CechTupleAlternatingHomotopy.cechTupleAlternatingProjection_single, one_smul]
        _ = baseCechTupleRow π M U i
              (Finsupp.single j (Equiv.Perm.sign s : ℤ)) := by
          rw [CechTupleAlternatingHomotopy.cechTupleAlternatingProjectionBasis_of_injective i hi]
        _ = (Equiv.Perm.sign s : ℤ) • (pj ≫ r) := by
          exact baseCechTupleRow_single_of_subset
            π M U i j (Equiv.Perm.sign s : ℤ) hji
    have hproj : OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF π M U n ≫ q = pj := by
      dsimp only [q, pj]
      exact OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF_comp_π π M U n ⟨j, hj⟩
    have halt :
        OrderedBaseCechAlternating.Scheme.Modules.orderedToBaseCechAlternatingF π M U n ≫ p =
          (Equiv.Perm.sign s : ℤ) • (q ≫ r) := by
      rw [hr]
      exact OrderedBaseCechAlternating.Scheme.Modules.orderedToBaseCechAlternatingF_comp_π_of_injective
        π M U n i hi
    rw [hleft]
    calc
      (Equiv.Perm.sign s : ℤ) • (pj ≫ r) =
          (Equiv.Perm.sign s : ℤ) •
            ((OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF π M U n ≫ q) ≫ r) := by
        rw [hproj]
      _ = OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF π M U n ≫
          ((Equiv.Perm.sign s : ℤ) • (q ≫ r)) := by
        simp only [comp_zsmul, Category.assoc]
      _ = OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF π M U n ≫
          (OrderedBaseCechAlternating.Scheme.Modules.orderedToBaseCechAlternatingF π M U n ≫ p) := by
        rw [halt]
  · have hleft :
        baseCechTupleMapF π M U
            (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n)
            (cechTupleAlternatingProjection_supportNonincreasing n) ≫ p = 0 := by
      calc
        baseCechTupleMapF π M U
              (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n)
              (cechTupleAlternatingProjection_supportNonincreasing n) ≫ p =
            baseCechTupleMapComponent π M U
              (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n)
              (cechTupleAlternatingProjection_supportNonincreasing n) i := by
          dsimp only [p]
          exact baseCechTupleMapF_comp_π π M U
            (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n)
              (cechTupleAlternatingProjection_supportNonincreasing n) i
        _ = 0 := by
          change baseCechTupleRow π M U i
              (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n
                (Finsupp.single i 1)) = 0
          rw [CechTupleAlternatingHomotopy.cechTupleAlternatingProjection_single, one_smul,
            CechTupleAlternatingHomotopy.cechTupleAlternatingProjectionBasis_of_not_injective i hi,
            map_zero]
    rw [hleft]
    rw [OrderedBaseCechAlternating.Scheme.Modules.orderedToBaseCechAlternatingF_comp_π_of_not_injective
      π M U n i hi]
    simp

/-- The zero tuple-chain map does not enlarge support. -/
theorem cechTupleSupportNonincreasing_zero
    {ι : Type u} {n m : ℕ} :
    CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing
      (0 : CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι m) := by
  intro i
  change CechTupleAlternatingHomotopy.CechTupleChain.SupportedBy 0 (Set.range i)
  exact CechTupleAlternatingHomotopy.CechTupleChain.supportedBy_zero

/-- The restriction lift sends the zero tuple-chain map to zero. -/
theorem baseCechTupleMapF_zero
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n m : ℕ) :
    baseCechTupleMapF π M U
        (0 : CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι m)
        cechTupleSupportNonincreasing_zero = 0 := by
  apply baseCechHom_ext π M U n
  intro i
  let p : (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n ⟶
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor π M U n q) i
  calc
    baseCechTupleMapF π M U 0
          cechTupleSupportNonincreasing_zero ≫ p =
        baseCechTupleMapComponent π M U 0
          cechTupleSupportNonincreasing_zero i := by
      dsimp only [p]
      exact baseCechTupleMapF_comp_π π M U 0
        cechTupleSupportNonincreasing_zero i
    _ = 0 := by
      change baseCechTupleRow π M U i
        ((0 : CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι m)
          (Finsupp.single i 1)) = 0
      simp
    _ = 0 ≫ p := by simp

/-- Equal support-nonincreasing tuple maps have equal restriction lifts. -/
theorem baseCechTupleMapF_congr
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f g : CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι m)
    (hf : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing f)
    (hg : CechTupleAlternatingHomotopy.CechTupleSupportNonincreasing g) (hfg : f = g) :
    baseCechTupleMapF π M U f hf =
      baseCechTupleMapF π M U g hg := by
  subst g
  rfl

/-- The tuple homotopy identity as an equality of integral linear maps. -/
theorem cechTupleAlternatingHomotopy_linear_identity
    {ι : Type u} [LinearOrder ι] (n : ℕ) :
    (CechTupleAlternatingHomotopy.cechTupleBoundary n).comp
          (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy n) +
        CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopyPrevious n =
      CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n +
        -(LinearMap.id :
          CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι n) := by
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.neg_apply, LinearMap.id_apply, sub_eq_add_neg]
    using CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy_identity n x

/-- The support-preserving tuple homotopy lifted to native base-Cech cochains. -/
noncomputable def baseCechAlternatingHomotopyF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X (n + 1) ⟶
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n :=
  baseCechTupleMapF π M U
    (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy n)
    (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy_supportNonincreasing n)

/-- The lifted lower-degree term `H d` in the native base-Cech homotopy identity. -/
noncomputable def baseCechAlternatingHomotopyPreviousF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n ⟶
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n :=
  baseCechTupleMapF π M U
    (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopyPrevious n)
    (cechTupleAlternatingHomotopyPrevious_supportNonincreasing n)

/-- The lifted tuple homotopy connects the ordered alternating retract to the identity. -/
theorem baseCechAlternatingHomotopy_identity
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d n (n + 1) ≫
          baseCechAlternatingHomotopyF π M U n +
        baseCechAlternatingHomotopyPreviousF π M U n =
      OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF π M U n ≫
          OrderedBaseCechAlternating.Scheme.Modules.orderedToBaseCechAlternatingF π M U n -
        𝟙 (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n := by
  let hdh :=
    CechTupleSupportNonincreasing.comp
      (cechTupleBoundary_supportNonincreasing (ι := ι) n)
      (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy_supportNonincreasing n)
  let hl :=
    CechTupleSupportNonincreasing.add hdh
      (cechTupleAlternatingHomotopyPrevious_supportNonincreasing n)
  let hr :=
    CechTupleSupportNonincreasing.add
      (cechTupleAlternatingProjection_supportNonincreasing n)
      (CechTupleSupportNonincreasing.neg
        (cechTupleSupportNonincreasing_id (ι := ι) (n := n)))
  have hlinear :=
    cechTupleAlternatingHomotopy_linear_identity
      (ι := ι) n
  have hlift :
      baseCechTupleMapF π M U
          ((CechTupleAlternatingHomotopy.cechTupleBoundary n).comp
              (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy n) +
            CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopyPrevious n) hl =
        baseCechTupleMapF π M U
          (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n +
            -(LinearMap.id :
              CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι n)) hr := by
    exact baseCechTupleMapF_congr π M U _ _ hl hr hlinear
  have hcomp :
      baseCechTupleMapF π M U
          ((CechTupleAlternatingHomotopy.cechTupleBoundary n).comp
            (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy n)) hdh =
        baseCechTupleMapF π M U
            (CechTupleAlternatingHomotopy.cechTupleBoundary n)
            (cechTupleBoundary_supportNonincreasing n) ≫
          baseCechTupleMapF π M U
            (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy n)
            (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy_supportNonincreasing n) := by
    exact baseCechTupleMapF_comp π M U
      (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy n)
      (CechTupleAlternatingHomotopy.cechTupleBoundary n)
      (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy_supportNonincreasing n)
      (cechTupleBoundary_supportNonincreasing n)
  calc
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d n (n + 1) ≫
          baseCechAlternatingHomotopyF π M U n +
        baseCechAlternatingHomotopyPreviousF π M U n =
      baseCechTupleMapF π M U
          ((CechTupleAlternatingHomotopy.cechTupleBoundary n).comp
              (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy n)) hdh +
        baseCechTupleMapF π M U
          (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopyPrevious n)
          (cechTupleAlternatingHomotopyPrevious_supportNonincreasing n) := by
      rw [hcomp, baseCechTupleMapF_boundary]
      rfl
    _ = baseCechTupleMapF π M U
          ((CechTupleAlternatingHomotopy.cechTupleBoundary n).comp
              (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy n) +
            CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopyPrevious n) hl := by
      exact (baseCechTupleMapF_add π M U _ _ _ _).symm
    _ = baseCechTupleMapF π M U
          (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n +
            -(LinearMap.id :
              CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι n)) hr := hlift
    _ = baseCechTupleMapF π M U
          (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n)
          (cechTupleAlternatingProjection_supportNonincreasing n) +
        baseCechTupleMapF π M U
          (-(LinearMap.id :
            CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι n))
          (CechTupleSupportNonincreasing.neg
            cechTupleSupportNonincreasing_id) := by
      exact baseCechTupleMapF_add π M U _ _ _ _
    _ = baseCechTupleMapF π M U
          (CechTupleAlternatingHomotopy.cechTupleAlternatingProjection n)
          (cechTupleAlternatingProjection_supportNonincreasing n) +
        -baseCechTupleMapF π M U
          (LinearMap.id :
            CechTupleAlternatingHomotopy.CechTupleChain ι n →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι n)
          cechTupleSupportNonincreasing_id := by
      rw [baseCechTupleMapF_neg]
    _ = OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF π M U n ≫
          OrderedBaseCechAlternating.Scheme.Modules.orderedToBaseCechAlternatingF π M U n -
        𝟙 (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X n := by
      rw [baseCechTupleMapF_alternatingProjection,
        baseCechTupleMapF_id]
      simp only [sub_eq_add_neg]

/-- The degree-zero lifted homotopy vanishes. -/
@[simp]
theorem baseCechAlternatingHomotopyF_zero
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    baseCechAlternatingHomotopyF π M U 0 = 0 := by
  change baseCechTupleMapF π M U
      (0 : CechTupleAlternatingHomotopy.CechTupleChain ι 0 →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι 1) _ = 0
  exact baseCechTupleMapF_zero π M U 0 1

/-- The degree-zero lower homotopy term vanishes. -/
@[simp]
theorem baseCechAlternatingHomotopyPreviousF_zero
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    baseCechAlternatingHomotopyPreviousF π M U 0 = 0 := by
  change baseCechTupleMapF π M U
      (0 : CechTupleAlternatingHomotopy.CechTupleChain ι 0 →ₗ[ℤ] CechTupleAlternatingHomotopy.CechTupleChain ι 0) _ = 0
  exact baseCechTupleMapF_zero π M U 0 0

/-- In positive degree the lower homotopy term is `H d`. -/
theorem baseCechAlternatingHomotopyPreviousF_succ
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    baseCechAlternatingHomotopyPreviousF π M U (n + 1) =
      baseCechAlternatingHomotopyF π M U n ≫
        (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d n (n + 1) := by
  change baseCechTupleMapF π M U
      ((CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy n).comp
        (CechTupleAlternatingHomotopy.cechTupleBoundary n)) _ =
    baseCechAlternatingHomotopyF π M U n ≫
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d n (n + 1)
  calc
    baseCechTupleMapF π M U
          ((CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy n).comp
            (CechTupleAlternatingHomotopy.cechTupleBoundary n)) _ =
        baseCechTupleMapF π M U
            (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy n)
            (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy_supportNonincreasing n) ≫
          baseCechTupleMapF π M U
            (CechTupleAlternatingHomotopy.cechTupleBoundary n)
            (cechTupleBoundary_supportNonincreasing n) := by
      exact baseCechTupleMapF_comp π M U
        (CechTupleAlternatingHomotopy.cechTupleBoundary n)
        (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy n)
        (cechTupleBoundary_supportNonincreasing n)
        (CechTupleAlternatingHomotopy.cechTupleAlternatingHomotopy_supportNonincreasing n)
    _ = baseCechAlternatingHomotopyF π M U n ≫
          (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d n (n + 1) := by
      rw [baseCechTupleMapF_boundary]
      rfl

/-- The base-Cech alternating homotopy equation in degree zero. -/
theorem baseCechAlternatingHomotopy_identity_zero
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d 0 1 ≫
        baseCechAlternatingHomotopyF π M U 0 =
      OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF π M U 0 ≫
          OrderedBaseCechAlternating.Scheme.Modules.orderedToBaseCechAlternatingF π M U 0 -
        𝟙 (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X 0 := by
  simpa using baseCechAlternatingHomotopy_identity π M U 0

/-- The base-Cech alternating homotopy equation in positive degree. -/
theorem baseCechAlternatingHomotopy_identity_succ
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d (n + 1) (n + 2) ≫
          baseCechAlternatingHomotopyF π M U (n + 1) +
        baseCechAlternatingHomotopyF π M U n ≫
          (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).d n (n + 1) =
      OrderedBaseCechComparison.Scheme.Modules.baseCechToOrderedF π M U (n + 1) ≫
          OrderedBaseCechAlternating.Scheme.Modules.orderedToBaseCechAlternatingF π M U (n + 1) -
        𝟙 (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).X (n + 1) := by
  rw [← baseCechAlternatingHomotopyPreviousF_succ π M U n]
  exact baseCechAlternatingHomotopy_identity π M U (n + 1)

end Scheme.Modules

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechTupleHomotopy
