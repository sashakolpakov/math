import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.InjectiveDifferential

/-! # Alternating Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AlternatingMap

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem orderedToCoefficientCechAlternatingF_comp_d
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
        (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) =
      Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential coefficientMap M U n ≫
        AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U (n + 1) := by
  apply Pi.hom_ext
  intro i
  let p : (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).X (n + 1) ⟶
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) i :=
    Pi.π (fun j : Fin (n + 2) → ι =>
      Ordered.CoefficientCechTerms.coefficientCechFactor coefficientMap M U (n + 1) j) i
  change (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
      (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1)) ≫ p =
    (Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential coefficientMap M U n ≫
      AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U (n + 1)) ≫ p
  by_cases hi : Function.Injective i
  · exact InjectiveDifferential.orderedToCoefficientCechAlternatingF_comp_d_comp_π_of_injective
      coefficientMap M U n i hi
  · have hleft :=
      DegenerateDifferential.orderedToCoefficientCechAlternatingF_comp_d_comp_π_of_not_injective
        coefficientMap M U n i hi
    change (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
      (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1)) ≫ p = 0 at hleft
    have hright := AlternatingRetraction.orderedToCoefficientCechAlternatingF_comp_π_of_not_injective
      coefficientMap M U (n + 1) i hi
    change AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U (n + 1) ≫ p = 0 at hright
    rw [hleft, Category.assoc, hright, comp_zero]

/-- The alternating extension from ordered Cech cochains to native Cech cochains. -/
noncomputable def orderedToCoefficientCechAlternating
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    Ordered.CoefficientCechComplex.orderedCoefficientCechComplex coefficientMap M U ⟶ Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U :=
  CochainComplex.ofHom (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U) fun n => by
    rw [Ordered.CoefficientCechComplex.orderedCoefficientCechComplex_d]
    exact orderedToCoefficientCechAlternatingF_comp_d coefficientMap M U n

@[simp]
theorem orderedToCoefficientCechAlternating_f
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (orderedToCoefficientCechAlternating coefficientMap M U).f n =
      AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n :=
  rfl

theorem orderedToCoefficientCechAlternating_comp_coefficientCechToOrdered
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    orderedToCoefficientCechAlternating coefficientMap M U ≫ OrderedCech.ComplexProjection.coefficientCechToOrdered coefficientMap M U =
      𝟙 (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex coefficientMap M U) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact AlternatingRetraction.orderedToCoefficientCechAlternatingF_comp_coefficientCechToOrderedF
    coefficientMap M U n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AlternatingMap
