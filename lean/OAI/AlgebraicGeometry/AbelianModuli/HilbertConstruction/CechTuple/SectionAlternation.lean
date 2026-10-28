/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionBoundary

/-! # Section Alternation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionAlternation

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- The restriction lift of signed sorting is projection to ordered tuples followed by
alternating extension. -/
theorem coefficientCechTupleMapF_alternatingProjection
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    SectionMaps.coefficientCechTupleMapF coefficientMap M U
        (FreeCech.TupleAlternation.cechTupleAlternatingProjection (ι := ι) n)
        (SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing n) =
      OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U n ≫
        CoefficientCech.AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n := by
  apply SectionIdentity.coefficientCechHom_ext coefficientMap M U n
  intro i
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n q) i
  change SectionMaps.coefficientCechTupleMapF coefficientMap M U
      (FreeCech.TupleAlternation.cechTupleAlternatingProjection n)
        (SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing n) ≫ p =
    (OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U n ≫
      CoefficientCech.AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n) ≫ p
  rw [Category.assoc]
  by_cases hi : Function.Injective i
  · let s := Tuple.sort i
    let j := i ∘ s
    have hj : StrictMono j :=
      (Tuple.monotone_sort i).strictMono_of_injective
        (hi.comp s.injective)
    let pj : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j :=
      Pi.π (fun q : Fin (n + 1) → ι =>
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n q) j
    let q : Ordered.CoefficientCechTerms.orderedCoefficientCechObject coefficientMap M U n ⟶
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j :=
      Pi.π (fun t : Ordered.SectionCechIndices.OrderedCechIndex ι n =>
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n t.1) ⟨j, hj⟩
    have hji : Set.range j ⊆ Set.range i := by
      rintro x ⟨k, rfl⟩
      exact ⟨s k, rfl⟩
    let r : Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n j ⟶
        Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
      SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U i j hji
    have hr :
        r = (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
          (((FormalCoproduct.mk _ U).mapPower s).φ i).op := by
      dsimp only [r]
      exact SectionRestrictions.coefficientCechTupleRestriction_eq_map coefficientMap M U i j hji
        (((FormalCoproduct.mk _ U).mapPower s).φ i)
    have hleft :
        SectionMaps.coefficientCechTupleMapF coefficientMap M U
            (FreeCech.TupleAlternation.cechTupleAlternatingProjection n)
            (SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing n) ≫ p =
          (Equiv.Perm.sign s : ℤ) • (pj ≫ r) := by
      calc
        SectionMaps.coefficientCechTupleMapF coefficientMap M U
              (FreeCech.TupleAlternation.cechTupleAlternatingProjection n)
              (SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing n) ≫ p =
            SectionMaps.coefficientCechTupleMapComponent coefficientMap M U
              (FreeCech.TupleAlternation.cechTupleAlternatingProjection n)
              (SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing n) i := by
          dsimp only [p]
          exact SectionMaps.coefficientCechTupleMapF_comp_π coefficientMap M U
            (FreeCech.TupleAlternation.cechTupleAlternatingProjection n)
              (SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing n) i
        _ = SectionRows.coefficientCechTupleRow coefficientMap M U i
              (FreeCech.TupleAlternation.cechTupleAlternatingProjectionBasis n i) := by
          change SectionRows.coefficientCechTupleRow coefficientMap M U i
              (FreeCech.TupleAlternation.cechTupleAlternatingProjection n
                (Finsupp.single i 1)) =
            SectionRows.coefficientCechTupleRow coefficientMap M U i
              (FreeCech.TupleAlternation.cechTupleAlternatingProjectionBasis n i)
          rw [FreeCech.TupleAlternation.cechTupleAlternatingProjection_single, one_smul]
        _ = SectionRows.coefficientCechTupleRow coefficientMap M U i
              (Finsupp.single j (Equiv.Perm.sign s : ℤ)) := by
          rw [FreeCech.TupleAlternation.cechTupleAlternatingProjectionBasis_of_injective i hi]
        _ = (Equiv.Perm.sign s : ℤ) • (pj ≫ r) := by
          exact SectionRows.coefficientCechTupleRow_single_of_subset
            coefficientMap M U i j (Equiv.Perm.sign s : ℤ) hji
    have hproj : OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U n ≫ q = pj := by
      dsimp only [q, pj]
      exact OrderedCech.ProjectionCoordinates.coefficientCechToOrderedF_comp_π coefficientMap M U n ⟨j, hj⟩
    have halt :
        CoefficientCech.AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫ p =
          (Equiv.Perm.sign s : ℤ) • (q ≫ r) := by
      rw [hr]
      exact CoefficientCech.AlternatingCoordinates.orderedToCoefficientCechAlternatingF_comp_π_of_injective
        coefficientMap M U n i hi
    rw [hleft]
    calc
      (Equiv.Perm.sign s : ℤ) • (pj ≫ r) =
          (Equiv.Perm.sign s : ℤ) •
            ((OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U n ≫ q) ≫ r) := by
        rw [hproj]
      _ = OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U n ≫
          ((Equiv.Perm.sign s : ℤ) • (q ≫ r)) := by
        simp only [comp_zsmul, Category.assoc]
      _ = OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U n ≫
          (CoefficientCech.AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫ p) := by
        rw [halt]
  · have hleft :
        SectionMaps.coefficientCechTupleMapF coefficientMap M U
            (FreeCech.TupleAlternation.cechTupleAlternatingProjection n)
            (SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing n) ≫ p = 0 := by
      calc
        SectionMaps.coefficientCechTupleMapF coefficientMap M U
              (FreeCech.TupleAlternation.cechTupleAlternatingProjection n)
              (SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing n) ≫ p =
            SectionMaps.coefficientCechTupleMapComponent coefficientMap M U
              (FreeCech.TupleAlternation.cechTupleAlternatingProjection n)
              (SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing n) i := by
          dsimp only [p]
          exact SectionMaps.coefficientCechTupleMapF_comp_π coefficientMap M U
            (FreeCech.TupleAlternation.cechTupleAlternatingProjection n)
              (SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing n) i
        _ = 0 := by
          change SectionRows.coefficientCechTupleRow coefficientMap M U i
              (FreeCech.TupleAlternation.cechTupleAlternatingProjection n
                (Finsupp.single i 1)) = 0
          rw [FreeCech.TupleAlternation.cechTupleAlternatingProjection_single, one_smul,
            FreeCech.TupleAlternation.cechTupleAlternatingProjectionBasis_of_not_injective i hi,
            map_zero]
    rw [hleft]
    rw [CoefficientCech.AlternatingRetraction.orderedToCoefficientCechAlternatingF_comp_π_of_not_injective
      coefficientMap M U n i hi]
    simp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionAlternation
