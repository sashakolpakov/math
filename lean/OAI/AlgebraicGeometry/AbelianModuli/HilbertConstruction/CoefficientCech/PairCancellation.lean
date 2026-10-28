/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AlternatingExtension

/-! # Pair Cancellation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.PairCancellation

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem orderedToCoefficientCechAlternatingF_comp_coface_π_pair
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hki : i k = i l) :
    AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) (i ∘ k.succAbove) ≫
        (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
          (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op =
      (Equiv.Perm.sign (Cech.DeletedTupleSigns.cechDeleteSwapPerm k l) : ℤ) •
        (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
          Pi.π (fun j : Fin (n + 1) → ι =>
            Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) (i ∘ l.succAbove) ≫
          (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
            (((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i).op) := by
  let ρ := Cech.DeletedTupleSigns.cechDeleteSwapPerm k l
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ l.succAbove) :=
    Pi.π (fun j : Fin (n + 1) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) (i ∘ l.succAbove)
  let r : Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ l.succAbove) ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) i :=
    (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
      (((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i).op
  let pk : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ k.succAbove) :=
    Pi.π (fun j : Fin (n + 1) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) (i ∘ k.succAbove)
  let rk : Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ k.succAbove) ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) i :=
    (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
      (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op
  have htuple : (i ∘ l.succAbove) ∘ ρ = i ∘ k.succAbove :=
    Cech.DeletedTupleSigns.comp_succAbove_cechDeleteSwapPerm_of_eq i k l hki
  let pρ : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n ((i ∘ l.succAbove) ∘ ρ) :=
    Pi.π (fun j : Fin (n + 1) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) ((i ∘ l.succAbove) ∘ ρ)
  let rρ : Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n ((i ∘ l.succAbove) ∘ ρ) ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ l.succAbove) :=
    (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
      (((FormalCoproduct.mk _ U).mapPower ρ).φ (i ∘ l.succAbove)).op
  have hρp : Permutations.coefficientCechPermutationF coefficientMap M U n ρ ≫ p = pρ ≫ rρ := by
    dsimp only [p, pρ, rρ]
    exact Permutations.coefficientCechPermutationF_comp_π
      coefficientMap M U n ρ (i ∘ l.succAbove)
  let a : (∏ᶜ fun x : Fin (n + 2) => U (i x)) ⟶
      ∏ᶜ fun x : Fin (n + 1) => U (((i ∘ l.succAbove) ∘ ρ) x) :=
    ((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i ≫
      ((FormalCoproduct.mk _ U).mapPower ρ).φ (i ∘ l.succAbove)
  let b : (∏ᶜ fun x : Fin (n + 2) => U (i x)) ⟶
      ∏ᶜ fun x : Fin (n + 1) => U ((i ∘ k.succAbove) x) :=
    ((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i
  have hrmaps : rρ ≫ r = (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map a.op := by
    let f := ((FormalCoproduct.mk _ U).mapPower ρ).φ (i ∘ l.succAbove)
    let g := ((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i
    change (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map f.op ≫
      (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map g.op =
        (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map (g ≫ f).op
    calc
      (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map f.op ≫
          (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map g.op =
        (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map (f.op ≫ g.op) :=
          ((Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map_comp f.op g.op).symm
      _ = (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map (g ≫ f).op := by
        exact congrArg (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
          (Subsingleton.elim _ _)
  have hproj : pρ ≫ (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map a.op =
      pk ≫ (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map b.op := by
    dsimp only [pρ, pk]
    exact AlternatingExtension.coefficientCechProjection_comp_map_eq_of_eq
      coefficientMap M U n ((i ∘ l.succAbove) ∘ ρ) (i ∘ k.succAbove)
        htuple a b
  have hrest : (pρ ≫ rρ) ≫ r = pk ≫ rk := by
    calc
      (pρ ≫ rρ) ≫ r = pρ ≫ (rρ ≫ r) := Category.assoc _ _ _
      _ = pρ ≫ (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map a.op := by rw [hrmaps]
      _ = pk ≫ (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map b.op := hproj
      _ = pk ≫ rk := by rfl
  have hface : Permutations.coefficientCechPermutationF coefficientMap M U n ρ ≫ p ≫ r = pk ≫ rk := by
    calc
      Permutations.coefficientCechPermutationF coefficientMap M U n ρ ≫ p ≫ r = (pρ ≫ rρ) ≫ r := by
        exact congrArg (fun f => f ≫ r) hρp
      _ = pk ≫ rk := hrest
  have hperm := AlternatingExtension.orderedToCoefficientCechAlternatingF_comp_permutation
    coefficientMap M U n ρ
  change AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫ pk ≫ rk =
    (Equiv.Perm.sign ρ : ℤ) •
      (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫ p ≫ r)
  calc
    AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫ pk ≫ rk =
        AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
          ((Permutations.coefficientCechPermutationF coefficientMap M U n ρ ≫ p) ≫ r) := by
      simp only [Category.assoc]
      rw [hface]
    _ = (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
        Permutations.coefficientCechPermutationF coefficientMap M U n ρ) ≫ (p ≫ r) := by
      simp only [Category.assoc]
    _ = ((Equiv.Perm.sign ρ : ℤ) •
        AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n) ≫ (p ≫ r) := by
      rw [hperm]
    _ = (Equiv.Perm.sign ρ : ℤ) •
        (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫ p ≫ r) := by
      rw [zsmul_comp]

theorem orderedToCoefficientCechAlternatingF_comp_coface_π_pair_cancel
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hki : i k = i l) (hkl : k ≠ l) :
    (-1 : ℤ) ^ (k : ℕ) •
        (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
          Pi.π (fun j : Fin (n + 1) → ι =>
            Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) (i ∘ k.succAbove) ≫
          (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
            (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op) +
      (-1 : ℤ) ^ (l : ℕ) •
        (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
          Pi.π (fun j : Fin (n + 1) → ι =>
            Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) (i ∘ l.succAbove) ≫
          (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
            (((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i).op) = 0 := by
  let t := AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
    Pi.π (fun j : Fin (n + 1) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) (i ∘ l.succAbove) ≫
    (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
      (((FormalCoproduct.mk _ U).mapPower l.succAbove).φ i).op
  have hpair := orderedToCoefficientCechAlternatingF_comp_coface_π_pair
    coefficientMap M U n i k l hki
  change (-1 : ℤ) ^ (k : ℕ) • _ + (-1 : ℤ) ^ (l : ℕ) • t = 0
  rw [hpair, smul_smul, Cech.DeletedTupleSigns.cechDeleteSwapPerm_sign k l hkl]
  have hcoef :
      (-1 : ℤ) ^ (k : ℕ) *
          -((-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (l : ℕ)) =
        -((-1 : ℤ) ^ (l : ℕ)) := by
    rw [mul_neg, ← mul_assoc, ← pow_add,
      (Even.add_self (k : ℕ)).neg_one_pow, one_mul]
  rw [hcoef, neg_smul, neg_add_cancel]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.PairCancellation
