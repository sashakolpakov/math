/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionRows

/-! # Section Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionMaps

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- Postcomposing a tuple row with restriction only changes its target tuple. -/
theorem coefficientCechTupleRow_comp_restriction
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (hji : Set.range j ⊆ Set.range i) (x : FreeCech.TupleChains.CechTupleChain ι l)
    (hx : FreeCech.TupleChains.CechTupleChain.SupportedBy x (Set.range j)) :
    SectionRows.coefficientCechTupleRow coefficientMap M U j x ≫
        SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U i j hji =
      SectionRows.coefficientCechTupleRow coefficientMap M U i x := by
  classical
  rw [SectionRows.coefficientCechTupleRow, SectionRows.coefficientCechTupleRow,
    Finsupp.lsum_apply, Finsupp.lsum_apply]
  rw [Finsupp.sum, Finsupp.sum, sum_comp]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj := hx hk
  simp only [LinearMap.toSpanSingleton_apply]
  rw [zsmul_comp,
    SectionRows.coefficientCechTupleRowBasis_comp_restriction
      coefficientMap M U i j k hkj hji]

/-- One row of the restriction matrix associated to a support-nonincreasing tuple-chain map. -/
noncomputable def coefficientCechTupleMapComponent
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f : FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι m)
    (_hf : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f)
    (i : Fin (n + 1) → ι) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X m ⟶ Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i :=
  SectionRows.coefficientCechTupleRow coefficientMap M U i (f (Finsupp.single i 1))

/-- The cochain map between two degrees dual to a support-nonincreasing tuple-chain map. -/
noncomputable def coefficientCechTupleMapF
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f : FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι m)
    (hf : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X m ⟶ (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n :=
  Pi.lift fun i => coefficientCechTupleMapComponent coefficientMap M U f hf i

theorem coefficientCechTupleMapF_comp_π
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f : FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι m)
    (hf : FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing f)
    (i : Fin (n + 1) → ι) :
    coefficientCechTupleMapF coefficientMap M U f hf ≫
        Pi.π (fun q : Fin (n + 1) → ι =>
          Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n q) i =
      coefficientCechTupleMapComponent coefficientMap M U f hf i :=
  Pi.lift_comp_π _ i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionMaps
