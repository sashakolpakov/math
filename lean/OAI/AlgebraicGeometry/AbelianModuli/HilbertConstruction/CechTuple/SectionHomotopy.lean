import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionZero

/-! # Section Homotopy -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionHomotopy

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- The support-preserving tuple homotopy lifted to native base-Cech cochains. -/
noncomputable def coefficientCechAlternatingHomotopyF
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X (n + 1) ⟶
      (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n :=
  SectionMaps.coefficientCechTupleMapF coefficientMap M U
    (FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n)
    (FreeCech.TupleHomotopySupport.cechTupleAlternatingHomotopy_supportNonincreasing n)

/-- The lifted lower-degree term `H d` in the native base-Cech homotopy identity. -/
noncomputable def coefficientCechAlternatingHomotopyPreviousF
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n ⟶
      (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n :=
  SectionMaps.coefficientCechTupleMapF coefficientMap M U
    (FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopyPrevious n)
    (SupportFunctoriality.cechTupleAlternatingHomotopyPrevious_supportNonincreasing n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionHomotopy
