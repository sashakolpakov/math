import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.ComplexPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.SheafificationPullbackSquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineCechCoordinateUnit

/-! # Coordinate Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CoordinatePullback.IntrinsicCechCoordinatePullback

noncomputable section

/-! The actual coordinate-form Čech pullback agrees with the actual sheaf direct-image pullback through the native sheafification unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Algebra ℚ R]
  {X Y : Over (Spec (CommRingCat.of R))} [IsSeparated X.hom] [IsSeparated Y.hom] (f : X ⟶ Y)
  {ι κ : Type} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

def coordinateMap : AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R Y U ⟶ AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X V :=
  Cech.ComplexPullback.CechPullback.bicomplexMap R f.left U V r hr (DeRham.Int.presheafPullback f)

def sheafPresheafMap :
    ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ)).obj
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) ⟶
      ((Cech.Image.CechImage.functor R f.left).mapHomologicalComplex (.up ℕ)).obj
        (((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ)).obj
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)) :=
  ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ)).map
    (DeRham.Int.sheafDirectImage f)

def sheafMap : CechBicomplex.IntrinsicCechBicomplex.bicomplex R Y U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) ⟶
    CechBicomplex.IntrinsicCechBicomplex.bicomplex R X V (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) :=
  Cech.ComplexPullback.CechPullback.bicomplexMap R f.left U V r hr (sheafPresheafMap R f)

omit [Algebra ℚ R] [IsSeparated X.hom] [IsSeparated Y.hom] in
theorem unit_square : Intrinsic.AffineCechCoordinateUnit.IntrinsicAffineCechCoordinateUnit.map R Y U ≫ sheafMap R f U V r hr =
    coordinateMap R f U V r hr ≫ Intrinsic.AffineCechCoordinateUnit.IntrinsicAffineCechCoordinateUnit.map R X V :=
  Cech.ComplexPullback.CechPullback.bicomplex_naturality R f.left U V r hr (DeRham.Int.presheafPullback f)
    (sheafPresheafMap R f)
    (SheafificationComplex.SheafificationComplexUnit.unit (Opens.grothendieckTopology Y.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y))
    (SheafificationComplex.SheafificationComplexUnit.unit (Opens.grothendieckTopology X.left) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X))
    (DeRham.SheafificationPullbackSquare.presheaf_sheaf_pullback_square f).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.CoordinatePullback.IntrinsicCechCoordinatePullback
