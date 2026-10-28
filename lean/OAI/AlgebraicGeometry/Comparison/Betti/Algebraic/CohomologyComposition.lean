import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.PullbackComposition
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.SingleComposition
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.CohomologyNaturality

/-! # Cohomology Composition -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CohomologyComposition

noncomputable section

/-! Composition of the original algebraic hypercohomology pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (g : Y ⟶ Z)

def derivedInverseImageCompIso : Sheaves.derivedInverseImage g ⋙ Sheaves.derivedInverseImage f ≅
    Sheaves.derivedInverseImage (f ≫ g) :=
  Derived.CompositeMap.compositeIso.{1, 1, 1} (Sheaves.inverseImage g) (Sheaves.inverseImage f) (Sheaves.inverseImage (f ≫ g))
    (PullbackComposition.inverseImageCompIso f g)

instance derivedInverseImageCompIsoCommShift : NatTrans.CommShift (derivedInverseImageCompIso f g).hom ℤ :=
  Derived.CompositeMap.compositeIsoCommShift (Sheaves.inverseImage g) (Sheaves.inverseImage f) (Sheaves.inverseImage (f ≫ g))
    (PullbackComposition.inverseImageCompIso f g)

theorem derivedDeRhamPullback_comp :
    (Sheaves.derivedInverseImage f).map (OpenForms.derivedDeRhamPullback g) ≫ OpenForms.derivedDeRhamPullback f =
      (derivedInverseImageCompIso f g).hom.app (DerivedCategory.Q.obj (Sheaves.algebraicDeRhamSheafComplexInt Z)) ≫
        OpenForms.derivedDeRhamPullback (f ≫ g) := by
  apply Derived.CompositeMap.derivedComplexMap_comp.{1, 1, 1}
    (Sheaves.inverseImage g) (Sheaves.inverseImage f) (Sheaves.inverseImage (f ≫ g)) (PullbackComposition.inverseImageCompIso f g)
    (OpenForms.deRhamSheafPullbackInt g) (OpenForms.deRhamSheafPullbackInt f) (OpenForms.deRhamSheafPullbackInt (f ≫ g))
  erw [PullbackComposition.inverseImageCompIso_onComplexes]
  exact PullbackComposition.deRhamSheafPullbackInt_comp f g

theorem derivedInverseImageConstantIso_comp :
    (Sheaves.derivedInverseImage f).map (OpenForms.derivedInverseImageConstantIso g).hom ≫
        (OpenForms.derivedInverseImageConstantIso f).hom =
      (derivedInverseImageCompIso f g).hom.app
          ((DerivedCategory.singleFunctor (Sheaves.ComplexSheaves Z) 0).obj (Sheaves.constantComplexSheaf Z)) ≫
        (OpenForms.derivedInverseImageConstantIso (f ≫ g)).hom :=
  Derived.SingleComposition.derivedSingleMap_comp.{1, 1, 1}
    (Sheaves.inverseImage g) (Sheaves.inverseImage f) (Sheaves.inverseImage (f ≫ g)) (PullbackComposition.inverseImageCompIso f g)
    (Sheaves.inverseImageConstantIso g).hom (Sheaves.inverseImageConstantIso f).hom
    (Sheaves.inverseImageConstantIso (f ≫ g)).hom (PullbackComposition.inverseImageCompIso_constant f g)

theorem algebraicDeRhamPullback_comp (n : ℕ) :
    OpenForms.algebraicDeRhamPullback g n ≫ OpenForms.algebraicDeRhamPullback f n = OpenForms.algebraicDeRhamPullback (f ≫ g) n := by
  ext a
  change OpenForms.algebraicDeRhamPullback f n (OpenForms.algebraicDeRhamPullback g n a) = OpenForms.algebraicDeRhamPullback (f ≫ g) n a
  erw [Analytic.CohomologyNaturality.algebraicDeRhamPullback_transport f n, Analytic.CohomologyNaturality.algebraicDeRhamPullback_transport g n,
    Analytic.CohomologyNaturality.algebraicDeRhamPullback_transport (f ≫ g) n]
  erw [ShiftedHomSquare.transport_comp (Sheaves.derivedInverseImage g) (Sheaves.derivedInverseImage f)]
  exact ShiftedHomSquare.transport_iso _ _ (derivedInverseImageCompIso f g)
    ((Sheaves.derivedInverseImage f).mapIso (OpenForms.derivedInverseImageConstantIso g) ≪≫ OpenForms.derivedInverseImageConstantIso f)
    (OpenForms.derivedInverseImageConstantIso (f ≫ g))
    ((Sheaves.derivedInverseImage f).map (OpenForms.derivedDeRhamPullback g) ≫ OpenForms.derivedDeRhamPullback f)
    (OpenForms.derivedDeRhamPullback (f ≫ g))
    (derivedInverseImageConstantIso_comp f g) (derivedDeRhamPullback_comp f g) a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CohomologyComposition
