import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AlternatingNullHomotopy
import Mathlib.Algebra.Homology.Homotopy

/-! # Coefficient Cech Homotopy Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechHomotopyEquivalence

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

/-- Projection to ordered tuples followed by alternating extension is homotopic
to the identity on the native base-Cech complex. -/
noncomputable def coefficientCechToOrdered_comp_orderedToCoefficientCechAlternating_homotopy
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    Homotopy
      (OrderedCech.ComplexProjection.coefficientCechToOrdered coefficientMap M U ≫
        CoefficientCech.AlternatingMap.orderedToCoefficientCechAlternating coefficientMap M U)
      (𝟙 (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U)) := by
  refine (Homotopy.equivSubZero
    (f := OrderedCech.ComplexProjection.coefficientCechToOrdered coefficientMap M U ≫
      CoefficientCech.AlternatingMap.orderedToCoefficientCechAlternating coefficientMap M U)
    (g := 𝟙 (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U))).symm ?_
  refine (Homotopy.ofEq
    (Cech.AlternatingNullHomotopy.coefficientCechAlternatingNullHomotopicMap_eq coefficientMap M U).symm).trans ?_
  exact Homotopy.nullHomotopy' fun i j h =>
    Cech.AlternatingNullHomotopy.coefficientCechAlternatingHomotopyComponent coefficientMap M U i j h

/-- The native and ordered base-Cech complexes are homotopy equivalent. -/
noncomputable def coefficientCechOrderedHomotopyEquiv
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    HomotopyEquiv
      (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U)
      (CoefficientCechComplex.orderedCoefficientCechComplex coefficientMap M U) where
  hom := OrderedCech.ComplexProjection.coefficientCechToOrdered coefficientMap M U
  inv := CoefficientCech.AlternatingMap.orderedToCoefficientCechAlternating coefficientMap M U
  homotopyHomInvId :=
    coefficientCechToOrdered_comp_orderedToCoefficientCechAlternating_homotopy coefficientMap M U
  homotopyInvHomId := Homotopy.ofEq
    (CoefficientCech.AlternatingMap.orderedToCoefficientCechAlternating_comp_coefficientCechToOrdered coefficientMap M U)

/-- Native and ordered base-Cech homology are isomorphic in every degree. -/
noncomputable def coefficientCechOrderedHomologyIso
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).homology n ≅
      (CoefficientCechComplex.orderedCoefficientCechComplex coefficientMap M U).homology n :=
  (coefficientCechOrderedHomotopyEquiv coefficientMap M U).toHomologyIso n

/-- Finite ordered base-Cech homology implies finite native base-Cech homology
in every degree. -/
theorem coefficientCechComplex_homology_module_finite_of_orderedCoefficientCechComplex
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    [Module.Finite R
      ((CoefficientCechComplex.orderedCoefficientCechComplex coefficientMap M U).homology n)] :
    Module.Finite R
      ((Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).homology n) :=
  Module.Finite.equiv
    (coefficientCechOrderedHomologyIso coefficientMap M U n).symm.toLinearEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechHomotopyEquivalence
