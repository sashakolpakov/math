import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.DegenerateDifferential

/-! # Ordered Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.OrderedDifferential

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem orderedToCoefficientCechAlternatingF_comp_d_comp_π_of_strictMono
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 2) → ι) (hi : StrictMono i) :
    AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
        (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) ≫
          Pi.π (fun j : Fin (n + 2) → ι =>
            Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) j) i =
      Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential coefficientMap M U n ≫
        AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U (n + 1) ≫
          Pi.π (fun j : Fin (n + 2) → ι =>
            Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) j) i := by
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X (n + 1) ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) i :=
    Pi.π (fun j : Fin (n + 2) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) j) i
  let q : Ordered.CoefficientCechTerms.orderedCoefficientCechObject coefficientMap M U (n + 1) ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) i :=
    Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι (n + 1) =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) j.1) ⟨i, hi⟩
  have hp : OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U (n + 1) ≫ q = p := by
    dsimp only [p, q]
    exact OrderedCech.ProjectionCoordinates.coefficientCechToOrderedF_comp_π coefficientMap M U (n + 1) ⟨i, hi⟩
  have ha : AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U (n + 1) ≫ p = q := by
    dsimp only [p, q]
    exact AlternatingCoordinates.orderedToCoefficientCechAlternatingF_comp_π_of_strictMono
      coefficientMap M U (n + 1) i hi
  change AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
      (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) ≫ p =
    Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential coefficientMap M U n ≫
      AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U (n + 1) ≫ p
  calc
    AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
        (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) ≫ p =
      AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
        ((Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) ≫
          OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U (n + 1)) ≫ q := by
        rw [Category.assoc, hp]
    _ = AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
        (OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U n ≫
          Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential coefficientMap M U n) ≫ q := by
      rw [OrderedCech.ComplexProjection.coefficientCechComplex_d_comp_coefficientCechToOrderedF]
    _ = (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
          OrderedCech.FormalProjection.coefficientCechToOrderedF coefficientMap M U n) ≫
        Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential coefficientMap M U n ≫ q := by
      simp only [Category.assoc]
    _ = Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential coefficientMap M U n ≫ q := by
      rw [AlternatingRetraction.orderedToCoefficientCechAlternatingF_comp_coefficientCechToOrderedF,
        Category.id_comp]
    _ = Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential coefficientMap M U n ≫
        AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U (n + 1) ≫ p := by
      rw [ha]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.OrderedDifferential
