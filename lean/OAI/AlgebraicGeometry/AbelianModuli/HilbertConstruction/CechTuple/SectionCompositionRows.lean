/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionAdditivity

/-! # Section Composition Rows -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionCompositionRows

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- A lifted tuple map commutes with one supported tuple-row basis vector. -/
theorem coefficientCechTupleMapF_comp_row_single
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (g : FreeCech.TupleChains.CechTupleChain ι m →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι l)
    (hg : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing g)
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (hji : Set.range j ⊆ Set.range i) :
    SectionMaps.coefficientCechTupleMapF coefficientMap M U g hg ≫
        SectionRows.coefficientCechTupleRow coefficientMap M U i (Finsupp.single j 1) =
      SectionRows.coefficientCechTupleRow coefficientMap M U i
        (g (Finsupp.single j 1)) := by
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X m ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U m j :=
    Pi.π (fun q : Fin (m + 1) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U m q) j
  have hrow :
      SectionRows.coefficientCechTupleRow coefficientMap M U i (Finsupp.single j 1) =
        p ≫ SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U i j hji := by
    rw [SectionRows.coefficientCechTupleRow_single_of_subset
      coefficientMap M U i j 1 hji, one_zsmul]
    rfl
  have hproj :
      SectionMaps.coefficientCechTupleMapF coefficientMap M U g hg ≫ p =
        SectionMaps.coefficientCechTupleMapComponent coefficientMap M U g hg j := by
    dsimp only [p]
    exact SectionMaps.coefficientCechTupleMapF_comp_π coefficientMap M U g hg j
  calc
    SectionMaps.coefficientCechTupleMapF coefficientMap M U g hg ≫
          SectionRows.coefficientCechTupleRow coefficientMap M U i (Finsupp.single j 1) =
        SectionMaps.coefficientCechTupleMapF coefficientMap M U g hg ≫
          (p ≫ SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U i j hji) := by
      rw [hrow]
    _ = (SectionMaps.coefficientCechTupleMapF coefficientMap M U g hg ≫ p) ≫
        SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U i j hji :=
      (Category.assoc _ _ _).symm
    _ = SectionMaps.coefficientCechTupleMapComponent coefficientMap M U g hg j ≫
        SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U i j hji := by
      rw [hproj]
    _ = SectionRows.coefficientCechTupleRow coefficientMap M U j
          (g (Finsupp.single j 1)) ≫
        SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U i j hji := rfl
    _ = SectionRows.coefficientCechTupleRow coefficientMap M U i
        (g (Finsupp.single j 1)) :=
      SectionMaps.coefficientCechTupleRow_comp_restriction coefficientMap M U i j hji
        (g (Finsupp.single j 1)) (hg j)

/-- A lifted tuple map commutes with every supported tuple row. -/
theorem coefficientCechTupleMapF_comp_row
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (g : FreeCech.TupleChains.CechTupleChain ι m →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι l)
    (hg : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing g)
    (i : Fin (n + 1) → ι) (x : FreeCech.TupleChains.CechTupleChain ι m)
    (hx : FreeCech.TupleChains.CechTupleChain.SupportedBy x (Set.range i)) :
    SectionMaps.coefficientCechTupleMapF coefficientMap M U g hg ≫
        SectionRows.coefficientCechTupleRow coefficientMap M U i x =
      SectionRows.coefficientCechTupleRow coefficientMap M U i (g x) := by
  classical
  have hsource := SupportFunctoriality.linearMap_apply_eq_finsupp_sum_single
    (SectionRows.coefficientCechTupleRow coefficientMap M U i) x
  have htarget := SupportFunctoriality.linearMap_apply_eq_finsupp_sum_single
    ((SectionRows.coefficientCechTupleRow coefficientMap M U i).comp g) x
  change SectionRows.coefficientCechTupleRow coefficientMap M U i (g x) =
    x.sum (fun j a => a • SectionRows.coefficientCechTupleRow coefficientMap M U i
      (g (Finsupp.single j 1))) at htarget
  rw [hsource, htarget]
  rw [Finsupp.sum, Finsupp.sum, comp_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [comp_zsmul,
    coefficientCechTupleMapF_comp_row_single coefficientMap M U g hg i j (hx hj)]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionCompositionRows
