import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IntegerComposition
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.CompositeMap
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.SingleComposition
import OAI.AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare

/-! # Composition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Composition

noncomputable section

/-! Composition of the independently constructed native algebraic de Rham cohomology pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {R : Type} [CommRing R]
  {X Y Z : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (g : Y ⟶ Z)

def derivedInverseImageCompIso : Int.derivedInverseImage g ⋙ Int.derivedInverseImage f ≅
    Int.derivedInverseImage (f ≫ g) :=
  AlgebraicGeometry.Comparison.Betti.Derived.CompositeMap.compositeIso.{1, 1, 1} (Int.inverseImage g) (Int.inverseImage f) (Int.inverseImage (f ≫ g))
    (ImageComposition.inverseImageCompIso f g)

instance derivedInverseImageCompIsoCommShift : NatTrans.CommShift (derivedInverseImageCompIso f g).hom ℤ :=
  AlgebraicGeometry.Comparison.Betti.Derived.CompositeMap.compositeIsoCommShift (Int.inverseImage g) (Int.inverseImage f) (Int.inverseImage (f ≫ g))
    (ImageComposition.inverseImageCompIso f g)

theorem derivedPullback_comp :
    (Int.derivedInverseImage f).map (Int.derivedPullback g) ≫ Int.derivedPullback f =
      (derivedInverseImageCompIso f g).hom.app (DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R Z)) ≫
        Int.derivedPullback (f ≫ g) :=
  AlgebraicGeometry.Comparison.Betti.Derived.CompositeMap.derivedComplexMap_comp.{1, 1, 1}
    (Int.inverseImage g) (Int.inverseImage f) (Int.inverseImage (f ≫ g)) (ImageComposition.inverseImageCompIso f g)
    (Int.sheafPullbackInt g) (Int.sheafPullbackInt f) (Int.sheafPullbackInt (f ≫ g)) (IntegerComposition.sheafPullbackInt_comp f g)

theorem derivedConstantIso_comp :
    (Int.derivedInverseImage f).map (Int.derivedConstantIso g).hom ≫ (Int.derivedConstantIso f).hom =
      (derivedInverseImageCompIso f g).hom.app
          ((DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Z) 0).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Z)) ≫
        (Int.derivedConstantIso (f ≫ g)).hom :=
  AlgebraicGeometry.Comparison.Betti.Derived.SingleComposition.derivedSingleMap_comp.{1, 1, 1}
    (Int.inverseImage g) (Int.inverseImage f) (Int.inverseImage (f ≫ g)) (ImageComposition.inverseImageCompIso f g)
    (Int.inverseImageConstantIso g).hom (Int.inverseImageConstantIso f).hom
    (Int.inverseImageConstantIso (f ≫ g)).hom (ImageComposition.inverseImageCompIso_constant f g)

theorem pullback_transport (n : ℕ) (a : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R Y n) :
    Int.pullback f n a =
      AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport (Int.derivedInverseImage f) (Int.derivedConstantIso f) (Int.derivedPullback f) a := by
  change (Int.derivedConstantIso f).inv ≫ (Int.derivedInverseImage f).map a ≫
    ((Int.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app _ ≫ (Int.derivedPullback f)⟦(n : ℤ)⟧' = _
  simp only [AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport, ShiftedHom.map, Category.assoc]

theorem pullback_comp (n : ℕ) : (Int.pullback f n).comp (Int.pullback g n) = Int.pullback (f ≫ g) n := by
  apply LinearMap.ext
  intro a
  change Int.pullback f n (Int.pullback g n a) = Int.pullback (f ≫ g) n a
  erw [pullback_transport f n, pullback_transport g n, pullback_transport (f ≫ g) n]
  erw [AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport_comp (Int.derivedInverseImage g) (Int.derivedInverseImage f)]
  exact AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport_iso _ _ (derivedInverseImageCompIso f g)
    ((Int.derivedInverseImage f).mapIso (Int.derivedConstantIso g) ≪≫ Int.derivedConstantIso f)
    (Int.derivedConstantIso (f ≫ g))
    ((Int.derivedInverseImage f).map (Int.derivedPullback g) ≫ Int.derivedPullback f)
    (Int.derivedPullback (f ≫ g)) (derivedConstantIso_comp f g) (derivedPullback_comp f g) a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Composition
