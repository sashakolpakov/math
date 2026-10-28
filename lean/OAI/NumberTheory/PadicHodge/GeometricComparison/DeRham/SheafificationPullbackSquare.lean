import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Int
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationComplex

/-! # Sheafification Pullback Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.SheafificationPullbackSquare

noncomputable section

/-! The actual native sheaf de Rham pullback is induced by the original presheaf form pullback through the canonical sheafification unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

theorem presheaf_sheaf_pullback_square :
    SheafificationComplex.SheafificationComplexUnit.unit (Opens.grothendieckTopology Y.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y) ≫
        ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ)).map
          (Int.sheafDirectImage f) =
      Int.presheafPullback f ≫ ((Int.directImagePresheaf f).mapHomologicalComplex (.up ℕ)).map
        (SheafificationComplex.SheafificationComplexUnit.unit (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)) := by
  let A := Int.sheafificationComplexAdjunction Y
  have h : A.homEquiv _ _ (Int.sheafDirectImage f) = Int.presheafToDirectImageSheafComplex f :=
    (A.homEquiv _ _).apply_symm_apply _
  exact (A.homEquiv_unit _ _ (Int.sheafDirectImage f)).symm.trans h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.SheafificationPullbackSquare
