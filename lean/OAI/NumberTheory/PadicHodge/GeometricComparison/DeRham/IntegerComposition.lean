import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.SheafComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExtensionComposition

/-! # Integer Composition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IntegerComposition

noncomputable section

/-! Composition of the actual extended de Rham sheaf pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {R : Type} [CommRing R]
  {X Y Z : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem sheafPullbackInt_comp :
    ((Int.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map (Int.sheafPullbackInt g) ≫
        Int.sheafPullbackInt f =
      (NatTrans.mapHomologicalComplex (ImageComposition.inverseImageCompIso f g).hom (ComplexShape.up ℤ)).app
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R Z) ≫ Int.sheafPullbackInt (f ≫ g) := by
  apply ExtensionComposition.FormsAdapter.extendedPullback_comp (Int.inverseImage g) (Int.inverseImage f)
    (Int.inverseImage (f ≫ g)) (ImageComposition.inverseImageCompIso f g) (Int.sheafPullback g) (Int.sheafPullback f)
    (Int.sheafPullback (f ≫ g)) ComplexShape.embeddingUpNat
  rw [ImageComposition.inverseImageCompIso_onComplexes]
  exact SheafComposition.sheafPullback_comp f g

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IntegerComposition
