import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionHomotopyIdentity

/-! # Section Homotopy Degrees -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionHomotopyDegrees

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- The degree-zero lifted homotopy vanishes. -/
@[simp]
theorem coefficientCechAlternatingHomotopyF_zero
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    SectionHomotopy.coefficientCechAlternatingHomotopyF coefficientMap M U 0 = 0 := by
  change SectionMaps.coefficientCechTupleMapF coefficientMap M U
      (0 : FreeCech.TupleChains.CechTupleChain ι 0 →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι 1) _ = 0
  exact SectionZero.coefficientCechTupleMapF_zero coefficientMap M U 0 1

/-- The degree-zero lower homotopy term vanishes. -/
@[simp]
theorem coefficientCechAlternatingHomotopyPreviousF_zero
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    SectionHomotopy.coefficientCechAlternatingHomotopyPreviousF coefficientMap M U 0 = 0 := by
  change SectionMaps.coefficientCechTupleMapF coefficientMap M U
      (0 : FreeCech.TupleChains.CechTupleChain ι 0 →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι 0) _ = 0
  exact SectionZero.coefficientCechTupleMapF_zero coefficientMap M U 0 0

/-- In positive degree the lower homotopy term is `H d`. -/
theorem coefficientCechAlternatingHomotopyPreviousF_succ
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    SectionHomotopy.coefficientCechAlternatingHomotopyPreviousF coefficientMap M U (n + 1) =
      SectionHomotopy.coefficientCechAlternatingHomotopyF coefficientMap M U n ≫
        (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) := by
  change SectionMaps.coefficientCechTupleMapF coefficientMap M U
      ((FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n).comp
        (FreeCech.TupleChains.cechTupleBoundary n)) _ =
    SectionHomotopy.coefficientCechAlternatingHomotopyF coefficientMap M U n ≫
      (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1)
  calc
    SectionMaps.coefficientCechTupleMapF coefficientMap M U
          ((FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n).comp
            (FreeCech.TupleChains.cechTupleBoundary n)) _ =
        SectionMaps.coefficientCechTupleMapF coefficientMap M U
            (FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n)
            (FreeCech.TupleHomotopySupport.cechTupleAlternatingHomotopy_supportNonincreasing n) ≫
          SectionMaps.coefficientCechTupleMapF coefficientMap M U
            (FreeCech.TupleChains.cechTupleBoundary n)
            (SupportFunctoriality.cechTupleBoundary_supportNonincreasing n) := by
      exact SectionComposition.coefficientCechTupleMapF_comp coefficientMap M U
        (FreeCech.TupleChains.cechTupleBoundary n)
        (FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n)
        (SupportFunctoriality.cechTupleBoundary_supportNonincreasing n)
        (FreeCech.TupleHomotopySupport.cechTupleAlternatingHomotopy_supportNonincreasing n)
    _ = SectionHomotopy.coefficientCechAlternatingHomotopyF coefficientMap M U n ≫
          (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) := by
      rw [SectionBoundary.coefficientCechTupleMapF_boundary]
      rfl

/-- The base-Cech alternating homotopy equation in degree zero. -/
theorem coefficientCechAlternatingHomotopy_identity_zero
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d 0 1 ≫
        SectionHomotopy.coefficientCechAlternatingHomotopyF coefficientMap M U 0 =
      OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U 0 ≫
          CoefficientCech.AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U 0 -
        𝟙 (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X 0 := by
  simpa using SectionHomotopyIdentity.coefficientCechAlternatingHomotopy_identity coefficientMap M U 0

/-- The base-Cech alternating homotopy equation in positive degree. -/
theorem coefficientCechAlternatingHomotopy_identity_succ
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d (n + 1) (n + 2) ≫
          SectionHomotopy.coefficientCechAlternatingHomotopyF coefficientMap M U (n + 1) +
        SectionHomotopy.coefficientCechAlternatingHomotopyF coefficientMap M U n ≫
          (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) =
      OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U (n + 1) ≫
          CoefficientCech.AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U (n + 1) -
        𝟙 (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X (n + 1) := by
  rw [← coefficientCechAlternatingHomotopyPreviousF_succ coefficientMap M U n]
  exact SectionHomotopyIdentity.coefficientCechAlternatingHomotopy_identity coefficientMap M U (n + 1)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionHomotopyDegrees
