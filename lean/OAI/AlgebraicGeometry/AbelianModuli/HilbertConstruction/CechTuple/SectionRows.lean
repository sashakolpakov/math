import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionRestrictions

/-! # Section Rows -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionRows

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- One basis entry in a tuple row, with unsupported entries discarded. -/
noncomputable def coefficientCechTupleRowBasis
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X m ⟶ Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i := by
  classical
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X m ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U m j :=
    Pi.π (fun q : Fin (m + 1) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U m q) j
  exact if h : Set.range j ⊆ Set.range i then
    p ≫ SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U i j h
  else 0

theorem coefficientCechTupleRowBasis_of_subset
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : Set.range j ⊆ Set.range i) :
    coefficientCechTupleRowBasis coefficientMap M U i j =
      Pi.π (fun q : Fin (m + 1) → ι =>
          Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U m q) j ≫
        SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U i j h := by
  classical
  simp [coefficientCechTupleRowBasis, h]
  congr

theorem coefficientCechTupleRowBasis_of_not_subset
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : ¬Set.range j ⊆ Set.range i) :
    coefficientCechTupleRowBasis coefficientMap M U i j = 0 := by
  classical
  simp [coefficientCechTupleRowBasis, h]

/-- A supported row-basis entry composes with tuple-factor restriction. -/
theorem coefficientCechTupleRowBasis_comp_restriction
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (k : Fin (l + 1) → ι) (hkj : Set.range k ⊆ Set.range j)
    (hji : Set.range j ⊆ Set.range i) :
    coefficientCechTupleRowBasis coefficientMap M U j k ≫
        SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U i j hji =
      coefficientCechTupleRowBasis coefficientMap M U i k := by
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X l ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U l k :=
    Pi.π (fun q : Fin (l + 1) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U l q) k
  calc
    coefficientCechTupleRowBasis coefficientMap M U j k ≫
          SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U i j hji =
        (p ≫ SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U j k hkj) ≫
          SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U i j hji := by
      rw [coefficientCechTupleRowBasis_of_subset coefficientMap M U j k hkj]
      rfl
    _ = p ≫
        (SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U j k hkj ≫
          SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U i j hji) :=
      Category.assoc _ _ _
    _ = p ≫ SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U i k
        (hkj.trans hji) := by
      rw [SectionRestrictions.coefficientCechTupleRestriction_comp]
    _ = coefficientCechTupleRowBasis coefficientMap M U i k := by
      rw [coefficientCechTupleRowBasis_of_subset
        coefficientMap M U i k (hkj.trans hji)]
      rfl

/-- A tuple chain defines a finite row of restriction maps. -/
noncomputable def coefficientCechTupleRow
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) :
    FreeCech.TupleChains.CechTupleChain ι m →ₗ[ℤ]
      ((Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X m ⟶ Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U n i) :=
  by
    exact Finsupp.lsum ℤ fun j =>
      LinearMap.toSpanSingleton ℤ _
        (coefficientCechTupleRowBasis coefficientMap M U i j)

theorem coefficientCechTupleRow_single_of_subset
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) (a : ℤ)
    (h : Set.range j ⊆ Set.range i) :
    coefficientCechTupleRow coefficientMap M U i (Finsupp.single j a) =
      a • (Pi.π (fun q : Fin (m + 1) → ι =>
          Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U m q) j ≫
        SectionRestrictions.coefficientCechTupleRestriction coefficientMap M U i j h) := by
  rw [coefficientCechTupleRow, Finsupp.lsum_single,
    LinearMap.toSpanSingleton_apply,
    coefficientCechTupleRowBasis_of_subset coefficientMap M U i j h]
  rfl

theorem coefficientCechTupleRow_single_of_not_subset
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) (a : ℤ)
    (h : ¬Set.range j ⊆ Set.range i) :
    coefficientCechTupleRow coefficientMap M U i (Finsupp.single j a) = 0 := by
  rw [coefficientCechTupleRow, Finsupp.lsum_single,
    LinearMap.toSpanSingleton_apply,
    coefficientCechTupleRowBasis_of_not_subset coefficientMap M U i j h,
    smul_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionRows
