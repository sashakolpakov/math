/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AlternatingRetraction

/-! # Alternating Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AlternatingCoordinates

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem orderedToCoefficientCechAlternatingF_comp_π_of_strictMono
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : StrictMono i) :
    AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) i =
      Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j.1) ⟨i, hi⟩ := by
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶ Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
    Pi.π (fun j : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) i
  let q : Ordered.CoefficientCechTerms.orderedCoefficientCechObject coefficientMap M U n ⟶ Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
    Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j.1) ⟨i, hi⟩
  have hp : OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U n ≫ q = p := by
    dsimp only [p, q]
    exact OrderedCech.ProjectionCoordinates.coefficientCechToOrderedF_comp_π coefficientMap M U n ⟨i, hi⟩
  change AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫ p = q
  calc
    AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫ p =
        AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
          (OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U n ≫ q) :=
      congrArg (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫ ·) hp.symm
    _ = (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
          OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U n) ≫ q :=
      (Category.assoc _ _ _).symm
    _ = q := by
      rw [AlternatingRetraction.orderedToCoefficientCechAlternatingF_comp_coefficientCechToOrderedF,
        Category.id_comp]

theorem orderedToCoefficientCechAlternatingF_comp_π_of_injective
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) (hi : Function.Injective i) :
    AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) i =
      (Equiv.Perm.sign (Tuple.sort i) : ℤ) •
        (Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
          Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j.1)
            ⟨i ∘ Tuple.sort i,
              (Tuple.monotone_sort i).strictMono_of_injective
                (hi.comp (Tuple.sort i).injective)⟩ ≫
          (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
            (((FormalCoproduct.mk _ U).mapPower (Tuple.sort i)).φ i).op) := by
  let s := Tuple.sort i
  have hs : StrictMono (i ∘ s) :=
    (Tuple.monotone_sort i).strictMono_of_injective
      (hi.comp s.injective)
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶ Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
    Pi.π (fun j : Fin (n + 1) → ι => Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) i
  let q : Ordered.CoefficientCechTerms.orderedCoefficientCechObject coefficientMap M U n ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ s) :=
    Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j.1) ⟨i ∘ s, hs⟩
  let r : Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ s) ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
    (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
      (((FormalCoproduct.mk _ U).mapPower s).φ i).op
  change AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫ p =
    (Equiv.Perm.sign s : ℤ) • (q ≫ r)
  rw [AlternatingExtension.orderedToCoefficientCechAlternatingF, sum_comp]
  rw [Finset.sum_eq_single s]
  · rw [zsmul_comp, Category.assoc, Permutations.coefficientCechPermutationF_comp_π]
    let ps : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ s) :=
      Pi.π (fun j : Fin (n + 1) → ι =>
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) (i ∘ s)
    have hz :
        OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF coefficientMap M U n ≫ ps = q := by
      dsimp only [ps, q]
      exact ZeroExtension.orderedToCoefficientCechZeroExtensionF_comp_π_of_strictMono
        coefficientMap M U n (i ∘ s) hs
    change (Equiv.Perm.sign s : ℤ) •
      (OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF coefficientMap M U n ≫ (ps ≫ r)) =
        (Equiv.Perm.sign s : ℤ) • (q ≫ r)
    have hpost :
        OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF coefficientMap M U n ≫ (ps ≫ r) = q ≫ r := by
      calc
        OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF coefficientMap M U n ≫ (ps ≫ r) =
            (OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF coefficientMap M U n ≫ ps) ≫ r :=
          (Category.assoc _ _ _).symm
        _ = q ≫ r := congrArg (· ≫ r) hz
    exact congrArg ((Equiv.Perm.sign s : ℤ) • ·) hpost
  · intro σ _ hne
    rw [zsmul_comp, Category.assoc, Permutations.coefficientCechPermutationF_comp_π]
    have hmono : ¬ StrictMono (i ∘ σ) := by
      intro h
      apply hne
      apply Equiv.ext
      intro x
      apply hi
      exact congrFun
        (Tuple.comp_sort_eq_comp_iff_monotone.mpr h.monotone) x
    have hz := ZeroExtension.orderedToCoefficientCechZeroExtensionF_comp_π_of_not_strictMono
      coefficientMap M U n (i ∘ σ) hmono
    let rσ : Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ σ) ⟶
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
      (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
        (((FormalCoproduct.mk _ U).mapPower σ).φ i).op
    let pσ : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ σ) :=
      Pi.π (fun j : Fin (n + 1) → ι =>
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) (i ∘ σ)
    change (Equiv.Perm.sign σ : ℤ) •
      (OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF coefficientMap M U n ≫ (pσ ≫ rσ)) = 0
    have hpost :
        OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF coefficientMap M U n ≫ (pσ ≫ rσ) = 0 := by
      calc
        OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF coefficientMap M U n ≫ (pσ ≫ rσ) =
            (OrderedCech.ProjectionSplitting.orderedToCoefficientCechZeroExtensionF coefficientMap M U n ≫ pσ) ≫ rσ :=
          (Category.assoc _ _ _).symm
        _ = 0 := by
          dsimp only [pσ]
          rw [hz, zero_comp]
    rw [hpost, smul_zero]
  · simp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AlternatingCoordinates
