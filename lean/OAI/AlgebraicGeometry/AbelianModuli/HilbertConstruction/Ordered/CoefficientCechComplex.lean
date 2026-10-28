/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechTerms
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Coefficient Cech Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechComplex

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace

universe u

/-- The alternating differential on ordered Cech cochains. -/
noncomputable def orderedCoefficientCechDifferential
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    CoefficientCechTerms.orderedCoefficientCechObject c M U n ⟶
      CoefficientCechTerms.orderedCoefficientCechObject c M U (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
    CoefficientCechTerms.orderedCoefficientCechCoface c M U n k

theorem orderedCoefficientCechDifferential_comp_π
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : SectionCechIndices.OrderedCechIndex ι (n + 1)) :
    orderedCoefficientCechDifferential c M U n ≫
        Pi.π (fun j : SectionCechIndices.OrderedCechIndex ι (n + 1) =>
          CoefficientCechTerms.coefficientCechFactor c M U (n + 1) j.1) i =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (Pi.π (fun j : SectionCechIndices.OrderedCechIndex ι n =>
          CoefficientCechTerms.coefficientCechFactor c M U n j.1) (i.delete k) ≫
          (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map
            (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op) := by
  let p : CoefficientCechTerms.orderedCoefficientCechObject c M U (n + 1) ⟶
      CoefficientCechTerms.coefficientCechFactor c M U (n + 1) i.1 :=
    Pi.π (fun j : SectionCechIndices.OrderedCechIndex ι (n + 1) =>
      CoefficientCechTerms.coefficientCechFactor c M U (n + 1) j.1) i
  change orderedCoefficientCechDifferential c M U n ≫ p = _
  rw [orderedCoefficientCechDifferential, sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [zsmul_comp, CoefficientCechTerms.orderedCoefficientCechCoface_comp_π]
  rfl

theorem orderedCoefficientCechDifferential_comp
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    orderedCoefficientCechDifferential c M U n ≫
      orderedCoefficientCechDifferential c M U (n + 1) = 0 := by
  dsimp [orderedCoefficientCechDifferential]
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  let P := Fin (n + 3) × Fin (n + 2)
  let T : Finset P := {ij : P | (ij.1 : ℕ) ≤ (ij.2 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl T,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ T → P := fun ij hij =>
    (ij.2.succ, Fin.castLT ij.1
      (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.2)))
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [T, φ, Finset.compl_filter, Finset.mem_filter_univ,
      Fin.val_succ, Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.snd h),
      by simpa [φ] using! congr_arg Prod.fst h⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [T, Finset.compl_filter, Finset.mem_filter_univ,
      not_le] at hij'
    refine ⟨(Fin.castSucc j', i'.pred (by
      rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij')), ?_, ?_⟩
    · simpa [T] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.succ_pred, Fin.castLT_castSucc]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, Fin.val_castLT, pow_add, pow_one,
        mul_neg, neg_mul, neg_neg, mul_one]
      apply mul_comm
    · rw [CoefficientCechTerms.orderedCoefficientCechCoface_comp' c M U n]
      simpa [T] using! hij

/-- The bounded ordered Cech cochain complex. -/
noncomputable def orderedCoefficientCechComplex
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (CoefficientCechTerms.orderedCoefficientCechObject c M U)
    (orderedCoefficientCechDifferential c M U)
    (orderedCoefficientCechDifferential_comp c M U)

@[simp]
theorem orderedCoefficientCechComplex_X
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (orderedCoefficientCechComplex c M U).X n = CoefficientCechTerms.orderedCoefficientCechObject c M U n :=
  rfl

@[simp]
theorem orderedCoefficientCechComplex_d
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (orderedCoefficientCechComplex c M U).d n (n + 1) =
      orderedCoefficientCechDifferential c M U n := by
  simp [orderedCoefficientCechComplex]

/-- The linear differential underlying the ordered Cech complex. -/
noncomputable abbrev orderedCoefficientCechLinearDifferential
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :=
  (orderedCoefficientCechDifferential c M U n).hom

theorem orderedCoefficientCechLinearDifferential_comp
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (orderedCoefficientCechLinearDifferential c M U (n + 1)).comp
      (orderedCoefficientCechLinearDifferential c M U n) = 0 := by
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    (orderedCoefficientCechDifferential_comp c M U n) x

/-- The ordered Cech complex vanishes above the cardinality of its finite cover. -/
theorem orderedCoefficientCechTerm_subsingleton_of_card_le
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (n : ℕ) (h : Fintype.card ι ≤ n) :
    Subsingleton (CoefficientCechTerms.orderedCoefficientCechTerm c M U n) := by
  let : IsEmpty (SectionCechIndices.OrderedCechIndex ι n) :=
    SectionCechIndices.isEmpty_orderedCechIndex_of_card_le ι n h
  infer_instance

/-- Ordered Cech objects vanish above the cardinality of the cover. -/
theorem orderedCoefficientCechObject_isZero_of_card_le
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (n : ℕ) (h : Fintype.card ι ≤ n) :
    IsZero (CoefficientCechTerms.orderedCoefficientCechObject c M U n) := by
  let : Subsingleton (CoefficientCechTerms.orderedCoefficientCechTerm c M U n) :=
    orderedCoefficientCechTerm_subsingleton_of_card_le c M U n h
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of R
      (CoefficientCechTerms.orderedCoefficientCechTerm c M U n))).of_iso
      (CoefficientCechTerms.orderedCoefficientCechObjectIsoPi c M U n)

/-- The ordered Cech complex is exact in every degree at least the cardinality
of its finite index type. -/
theorem orderedCoefficientCechComplex_exactAt_of_card_le
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (n : ℕ) (h : Fintype.card ι ≤ n) :
    (orderedCoefficientCechComplex c M U).ExactAt n := by
  let C := orderedCoefficientCechComplex c M U
  have hX : IsZero (C.X n) := by
    dsimp only [C, orderedCoefficientCechComplex]
    exact orderedCoefficientCechObject_isZero_of_card_le c M U n h
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.isZero_homology_of_isZero_X₂ (C.sc n) hX

/-- The underlying module of an ordered Cech object is subsingleton above the
cardinality of the cover. -/
theorem orderedCoefficientCechObject_subsingleton_of_card_le
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (n : ℕ) (h : Fintype.card ι ≤ n) :
    Subsingleton (CoefficientCechTerms.orderedCoefficientCechObject c M U n) :=
  ModuleCat.subsingleton_of_isZero
    (orderedCoefficientCechObject_isZero_of_card_le c M U n h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechComplex
