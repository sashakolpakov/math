/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AlternatingDifferentialSymmetry

/-! # Degenerate Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.DegenerateDifferential

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem orderedToCoefficientCechAlternatingF_comp_d_comp_π_of_not_injective
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 2) → ι) (hi : ¬ Function.Injective i) :
    AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
        (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) ≫
          Pi.π (fun j : Fin (n + 2) → ι =>
            Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) j) i = 0 := by
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X (n + 1) ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) i :=
    Pi.π (fun j : Fin (n + 2) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) j) i
  change AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
    ((Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) ≫ p) = 0
  let G : Fin (n + 2) →
      ((Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶ Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) i) :=
    fun k => (-1 : ℤ) ^ (k : ℕ) •
      (Pi.π (fun j : Fin (n + 1) → ι =>
          Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) (i ∘ k.succAbove) ≫
        (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
          (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op)
  let F : Fin (n + 2) →
      (Ordered.CoefficientCechTerms.orderedCoefficientCechObject coefficientMap M U n ⟶ Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) i) :=
    fun k => (-1 : ℤ) ^ (k : ℕ) •
      (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) (i ∘ k.succAbove) ≫
        (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
          (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op)
  have hd : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) ≫ p = ∑ k, G k := by
    dsimp only [p, G]
    exact OrderedCech.ComplexProjection.coefficientCechComplex_d_comp_π coefficientMap M U n i
  have hcomp : AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫ (∑ k, G k) =
      ∑ k, AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫ G k := by
    simpa using comp_sum (Finset.univ : Finset (Fin (n + 2)))
      (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n) G
  have hterms : (∑ k, AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫ G k) =
      ∑ k, F k := by
    apply Finset.sum_congr rfl
    intro k _
    let q : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) i :=
      Pi.π (fun j : Fin (n + 1) → ι =>
          Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) (i ∘ k.succAbove) ≫
        (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
          (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op
    change AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
      ((-1 : ℤ) ^ (k : ℕ) • q) =
        (-1 : ℤ) ^ (k : ℕ) •
          (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫ q)
    exact comp_zsmul _ _ ((-1 : ℤ) ^ (k : ℕ))
  rw [hd, hcomp, hterms]
  by_cases hall : ∀ k : Fin (n + 2),
      ¬ Function.Injective (i ∘ k.succAbove)
  · apply Finset.sum_eq_zero
    intro k _
    let q : Ordered.CoefficientCechTerms.orderedCoefficientCechObject coefficientMap M U n ⟶
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ k.succAbove) :=
      AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) (i ∘ k.succAbove)
    let r : Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ k.succAbove) ⟶
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) i :=
      (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
        (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op
    have hk := AlternatingRetraction.orderedToCoefficientCechAlternatingF_comp_π_of_not_injective
      coefficientMap M U n (i ∘ k.succAbove) (hall k)
    change (-1 : ℤ) ^ (k : ℕ) • (q ≫ r) = 0
    change q = 0 at hk
    rw [hk, zero_comp, smul_zero]
  · have hex : ∃ k : Fin (n + 2),
        Function.Injective (i ∘ k.succAbove) := by
      by_contra h
      apply hall
      intro k hk
      exact h ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hex
    obtain ⟨l, hlk, hil⟩ := Cech.RepeatedTuplePartners.exists_partner_of_delete_injective i hi k hk
    have hkl : k ≠ l := hlk.symm
    have hother (m : Fin (n + 2)) (hmk : m ≠ k) (hml : m ≠ l) :
        F m = 0 := by
      let q : Ordered.CoefficientCechTerms.orderedCoefficientCechObject coefficientMap M U n ⟶
          Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ m.succAbove) :=
        AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
          Pi.π (fun j : Fin (n + 1) → ι =>
            Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j) (i ∘ m.succAbove)
      let r : Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n (i ∘ m.succAbove) ⟶
          Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) i :=
        (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
          (((FormalCoproduct.mk _ U).mapPower m.succAbove).φ i).op
      have hm := Cech.RepeatedTuplePartners.delete_not_injective_of_ne i k l m hkl hmk.symm hml.symm hil
      have hz := AlternatingRetraction.orderedToCoefficientCechAlternatingF_comp_π_of_not_injective
        coefficientMap M U n (i ∘ m.succAbove) hm
      change (-1 : ℤ) ^ (m : ℕ) • (q ≫ r) = 0
      change q = 0 at hz
      rw [hz, zero_comp, smul_zero]
    have hrem : ((Finset.univ.erase l).erase k).sum F = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hmk : m ≠ k := (Finset.mem_erase.mp hm).1
      have hml : m ≠ l :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1
      exact hother m hmk hml
    have hk_mem : k ∈ Finset.univ.erase l :=
      Finset.mem_erase.mpr ⟨hkl, Finset.mem_univ k⟩
    calc
      ∑ m, F m = (Finset.univ.erase l).sum F + F l :=
        (Finset.sum_erase_add Finset.univ F (Finset.mem_univ l)).symm
      _ = (((Finset.univ.erase l).erase k).sum F + F k) + F l := by
        rw [Finset.sum_erase_add (Finset.univ.erase l) F hk_mem]
      _ = F k + F l := by rw [hrem, zero_add]
      _ = 0 := by
        dsimp only [F]
        exact PairCancellation.orderedToCoefficientCechAlternatingF_comp_coface_π_pair_cancel
          coefficientMap M U n i k l hil.symm hkl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.DegenerateDifferential
