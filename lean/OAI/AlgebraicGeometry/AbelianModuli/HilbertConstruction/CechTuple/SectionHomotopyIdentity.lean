import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionHomotopy

/-! # Section Homotopy Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionHomotopyIdentity

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

open Set

/-- The lifted tuple homotopy connects the ordered alternating retract to the identity. -/
theorem coefficientCechAlternatingHomotopy_identity
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) ≫
          SectionHomotopy.coefficientCechAlternatingHomotopyF coefficientMap M U n +
        SectionHomotopy.coefficientCechAlternatingHomotopyPreviousF coefficientMap M U n =
      OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U n ≫
          CoefficientCech.AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n -
        𝟙 (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n := by
  let hdh :=
    FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.comp
      (SupportFunctoriality.cechTupleBoundary_supportNonincreasing (ι := ι) n)
      (FreeCech.TupleHomotopySupport.cechTupleAlternatingHomotopy_supportNonincreasing n)
  let hl :=
    FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.add hdh
      (SupportFunctoriality.cechTupleAlternatingHomotopyPrevious_supportNonincreasing n)
  let hr :=
    FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.add
      (SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing n)
      (FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.neg
        (SupportFunctoriality.cechTupleSupportNonincreasing_id (ι := ι) (n := n)))
  have hlinear :=
    SectionZero.cechTupleAlternatingHomotopy_linear_identity
      (ι := ι) n
  have hlift :
      SectionMaps.coefficientCechTupleMapF coefficientMap M U
          ((FreeCech.TupleChains.cechTupleBoundary n).comp
              (FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n) +
            FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopyPrevious n) hl =
        SectionMaps.coefficientCechTupleMapF coefficientMap M U
          (FreeCech.TupleAlternation.cechTupleAlternatingProjection n +
            -(LinearMap.id :
              FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι n)) hr := by
    exact SectionZero.coefficientCechTupleMapF_congr coefficientMap M U _ _ hl hr hlinear
  have hcomp :
      SectionMaps.coefficientCechTupleMapF coefficientMap M U
          ((FreeCech.TupleChains.cechTupleBoundary n).comp
            (FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n)) hdh =
        SectionMaps.coefficientCechTupleMapF coefficientMap M U
            (FreeCech.TupleChains.cechTupleBoundary n)
            (SupportFunctoriality.cechTupleBoundary_supportNonincreasing n) ≫
          SectionMaps.coefficientCechTupleMapF coefficientMap M U
            (FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n)
            (FreeCech.TupleHomotopySupport.cechTupleAlternatingHomotopy_supportNonincreasing n) := by
    exact SectionComposition.coefficientCechTupleMapF_comp coefficientMap M U
      (FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n)
      (FreeCech.TupleChains.cechTupleBoundary n)
      (FreeCech.TupleHomotopySupport.cechTupleAlternatingHomotopy_supportNonincreasing n)
      (SupportFunctoriality.cechTupleBoundary_supportNonincreasing n)
  calc
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) ≫
          SectionHomotopy.coefficientCechAlternatingHomotopyF coefficientMap M U n +
        SectionHomotopy.coefficientCechAlternatingHomotopyPreviousF coefficientMap M U n =
      SectionMaps.coefficientCechTupleMapF coefficientMap M U
          ((FreeCech.TupleChains.cechTupleBoundary n).comp
              (FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n)) hdh +
        SectionMaps.coefficientCechTupleMapF coefficientMap M U
          (FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopyPrevious n)
          (SupportFunctoriality.cechTupleAlternatingHomotopyPrevious_supportNonincreasing n) := by
      rw [hcomp, SectionBoundary.coefficientCechTupleMapF_boundary]
      rfl
    _ = SectionMaps.coefficientCechTupleMapF coefficientMap M U
          ((FreeCech.TupleChains.cechTupleBoundary n).comp
              (FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopy n) +
            FreeCech.TupleRecursiveHomotopy.cechTupleAlternatingHomotopyPrevious n) hl := by
      exact (SectionAdditivity.coefficientCechTupleMapF_add coefficientMap M U _ _ _ _).symm
    _ = SectionMaps.coefficientCechTupleMapF coefficientMap M U
          (FreeCech.TupleAlternation.cechTupleAlternatingProjection n +
            -(LinearMap.id :
              FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι n)) hr := hlift
    _ = SectionMaps.coefficientCechTupleMapF coefficientMap M U
          (FreeCech.TupleAlternation.cechTupleAlternatingProjection n)
          (SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing n) +
        SectionMaps.coefficientCechTupleMapF coefficientMap M U
          (-(LinearMap.id :
            FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι n))
          (FreeCech.TupleHomotopySupport.CechTupleSupportNonincreasing.neg
            SupportFunctoriality.cechTupleSupportNonincreasing_id) := by
      exact SectionAdditivity.coefficientCechTupleMapF_add coefficientMap M U _ _ _ _
    _ = SectionMaps.coefficientCechTupleMapF coefficientMap M U
          (FreeCech.TupleAlternation.cechTupleAlternatingProjection n)
          (SupportFunctoriality.cechTupleAlternatingProjection_supportNonincreasing n) +
        -SectionMaps.coefficientCechTupleMapF coefficientMap M U
          (LinearMap.id :
            FreeCech.TupleChains.CechTupleChain ι n →ₗ[ℤ] FreeCech.TupleChains.CechTupleChain ι n)
          SupportFunctoriality.cechTupleSupportNonincreasing_id := by
      rw [SectionAdditivity.coefficientCechTupleMapF_neg]
    _ = OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U n ≫
          CoefficientCech.AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n -
        𝟙 (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X n := by
      rw [SectionAlternation.coefficientCechTupleMapF_alternatingProjection,
        SectionIdentity.coefficientCechTupleMapF_id]
      simp only [sub_eq_add_neg]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CechTuple.SectionHomotopyIdentity
