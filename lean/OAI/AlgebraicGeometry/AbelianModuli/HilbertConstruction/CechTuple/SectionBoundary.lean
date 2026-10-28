/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionComposition

/-! # Section Boundary -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionBoundary

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- Deleting an entry does not introduce a new tuple index. -/
theorem cechTupleDelete_range_subset
    {ι : Type u} {n : ℕ} (i : Fin (n + 2) → ι)
    (k : Fin (n + 2)) :
    Set.range (FreeCech.TupleChains.cechTupleDelete i k) ⊆ Set.range i := by
  rintro x ⟨l, rfl⟩
  exact ⟨k.succAbove l, rfl⟩

/-- The restriction lift of the tuple boundary is the native base-Cech differential. -/
theorem coefficientCechTupleMapF_boundary
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    SectionMaps.coefficientCechTupleMapF coefficientMap M U
        (FreeCech.TupleChains.cechTupleBoundary (ι := ι) n)
        (SupportFunctoriality.cechTupleBoundary_supportNonincreasing n) =
      (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) := by
  apply SectionIdentity.coefficientCechHom_ext coefficientMap M U (n + 1)
  intro i
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X (n + 1) ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) i :=
    Pi.π (fun q : Fin (n + 2) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) q) i
  let t : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) i :=
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
      (Pi.π (fun q : Fin (n + 1) → ι =>
          Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n q)
            (FreeCech.TupleChains.cechTupleDelete i k) ≫
        (Coefficient.ModulePresheaf.coefficientModulePresheaf coefficientMap M).map
          (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op)
  have hcomponent :
      SectionMaps.coefficientCechTupleMapComponent coefficientMap M U
          (FreeCech.TupleChains.cechTupleBoundary (ι := ι) n)
          (SupportFunctoriality.cechTupleBoundary_supportNonincreasing n) i = t := by
    change SectionRows.coefficientCechTupleRow coefficientMap M U i
        (FreeCech.TupleChains.cechTupleBoundary n (Finsupp.single i 1)) = t
    rw [FreeCech.TupleChains.cechTupleBoundary_single, one_smul]
    unfold FreeCech.TupleChains.cechTupleBoundaryBasis
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    let h := cechTupleDelete_range_subset i k
    rw [SectionRows.coefficientCechTupleRow_single_of_subset
      coefficientMap M U i (FreeCech.TupleChains.cechTupleDelete i k)
        ((-1 : ℤ) ^ (k : ℕ)) h]
    congr 2
  calc
    SectionMaps.coefficientCechTupleMapF coefficientMap M U (FreeCech.TupleChains.cechTupleBoundary n)
          (SupportFunctoriality.cechTupleBoundary_supportNonincreasing n) ≫ p =
        SectionMaps.coefficientCechTupleMapComponent coefficientMap M U (FreeCech.TupleChains.cechTupleBoundary n)
          (SupportFunctoriality.cechTupleBoundary_supportNonincreasing n) i := by
      dsimp only [p]
      exact SectionMaps.coefficientCechTupleMapF_comp_π coefficientMap M U
        (FreeCech.TupleChains.cechTupleBoundary n)
          (SupportFunctoriality.cechTupleBoundary_supportNonincreasing n) i
    _ = t := hcomponent
    _ = (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) ≫ p := by
      dsimp only [t, p]
      rw [OrderedCech.ComplexProjection.coefficientCechComplex_d_comp_π]
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

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionBoundary
