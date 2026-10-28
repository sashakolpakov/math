/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.OrderedDifferential

/-! # Injective Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.InjectiveDifferential

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem orderedToCoefficientCechAlternatingF_comp_d_comp_π_of_injective
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 2) → ι) (hi : Function.Injective i) :
    AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
        (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) ≫
          Pi.π (fun j : Fin (n + 2) → ι =>
            Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) j) i =
      Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential coefficientMap M U n ≫
        AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U (n + 1) ≫
          Pi.π (fun j : Fin (n + 2) → ι =>
            Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) j) i := by
  let σ := Tuple.sort i
  let j := i ∘ σ
  have hj : StrictMono j :=
    (Tuple.monotone_sort i).strictMono_of_injective
      (hi.comp σ.injective)
  let A : Ordered.CoefficientCechTerms.orderedCoefficientCechObject coefficientMap M U n ⟶
      (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X (n + 1) :=
    AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
      (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1)
  let B := AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U (n + 1)
  let D := Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential coefficientMap M U n
  let P := Permutations.coefficientCechPermutationF coefficientMap M U (n + 1) σ
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X (n + 1) ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) i :=
    Pi.π (fun q : Fin (n + 2) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) q) i
  let pj : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X (n + 1) ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) j :=
    Pi.π (fun q : Fin (n + 2) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) q) j
  let q : Ordered.CoefficientCechTerms.orderedCoefficientCechObject coefficientMap M U (n + 1) ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) j :=
    Pi.π (fun t : Ordered.SectionCechIndices.OrderedCechIndex ι (n + 1) =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) t.1) ⟨j, hj⟩
  let r : Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) j ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) i :=
    (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
      (((FormalCoproduct.mk _ U).mapPower σ).φ i).op
  let s : ℤ := Equiv.Perm.sign σ
  have hPp : P ≫ p = pj ≫ r := by
    dsimp only [P, p, pj, r, j]
    exact Permutations.coefficientCechPermutationF_comp_π coefficientMap M U (n + 1) σ i
  have hAperm := AlternatingDifferentialSymmetry.orderedToCoefficientCechAlternatingF_comp_d_comp_permutation
    coefficientMap M U n σ
  change A ≫ P = s • A at hAperm
  have hrel : A ≫ pj ≫ r = s • (A ≫ p) := by
    calc
      A ≫ pj ≫ r = A ≫ (P ≫ p) := by rw [hPp]
      _ = (A ≫ P) ≫ p := by simp only [Category.assoc]
      _ = (s • A) ≫ p := by rw [hAperm]
      _ = s • (A ≫ p) := by rw [zsmul_comp]
  have hs : s * s = 1 := by
    dsimp only [s]
    exact Int.units_coe_mul_self (Equiv.Perm.sign σ)
  have hrel' : A ≫ p = s • (A ≫ pj ≫ r) := by
    calc
      A ≫ p = s • (s • (A ≫ p)) := by
        rw [smul_smul, hs, one_smul]
      _ = s • (A ≫ pj ≫ r) := congrArg (s • ·) hrel.symm
  have hstrict :=
    OrderedDifferential.orderedToCoefficientCechAlternatingF_comp_d_comp_π_of_strictMono
      coefficientMap M U n j hj
  change A ≫ pj = D ≫ B ≫ pj at hstrict
  have hBj := AlternatingCoordinates.orderedToCoefficientCechAlternatingF_comp_π_of_strictMono
    coefficientMap M U (n + 1) j hj
  change B ≫ pj = q at hBj
  have hBi := AlternatingCoordinates.orderedToCoefficientCechAlternatingF_comp_π_of_injective
    coefficientMap M U (n + 1) i hi
  change B ≫ p = s • (q ≫ r) at hBi
  have hstrict_r : (A ≫ pj) ≫ r = (D ≫ B ≫ pj) ≫ r :=
    congrArg (fun f => f ≫ r) hstrict
  have hDj : D ≫ B ≫ pj = D ≫ q :=
    congrArg (D ≫ ·) hBj
  have hDj_r : (D ≫ B ≫ pj) ≫ r = (D ≫ q) ≫ r :=
    congrArg (fun f => f ≫ r) hDj
  change A ≫ p = D ≫ B ≫ p
  calc
    A ≫ p = s • (A ≫ pj ≫ r) := hrel'
    _ = s • ((D ≫ B ≫ pj) ≫ r) := congrArg (s • ·) hstrict_r
    _ = s • ((D ≫ q) ≫ r) := congrArg (s • ·) hDj_r
    _ = D ≫ (s • (q ≫ r)) := by
      calc
        s • ((D ≫ q) ≫ r) = s • (D ≫ (q ≫ r)) :=
          congrArg (s • ·) (Category.assoc D q r)
        _ = D ≫ (s • (q ≫ r)) :=
          (comp_zsmul D (q ≫ r) s).symm
    _ = D ≫ (B ≫ p) := by rw [hBi]
    _ = D ≫ B ≫ p := by rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.InjectiveDifferential
