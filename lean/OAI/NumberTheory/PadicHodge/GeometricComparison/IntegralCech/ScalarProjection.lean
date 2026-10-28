import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechScalarBicomplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarProjection

/-! # Scalar Projection -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.ScalarProjection.IntegralCechScalarProjection

noncomputable section

/-! The actual scalar map on the first-three Cech bicomplex agrees with the
original full scalar map in its retained rows. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  {ι : Type} [Finite ι] (U : ι → X.left.Opens)

def map : IntegralFirst.ThreeCechScalarBicomplex.IntegralFirstThreeCechScalarBicomplex.source R S X U ⟶
    IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex S Y (fun i => f ⁻¹ᵁ U i) :=
  (IntegralFirst.ThreeCechScalarBicomplex.IntegralFirstThreeCechScalarBicomplex.coefficientIso R S X U).hom ≫
    IntegralFirst.ThreeCechScalarBicomplex.IntegralFirstThreeCechScalarBicomplex.map R S X Y f U h ≫
      (IntegralFirst.ThreeCechScalarBicomplex.IntegralFirstThreeCechScalarBicomplex.inverseImageIso R S X Y f U).hom

theorem row_zero : (IntegralCechScalarProjection.map R S X Y f h U).f 0 = (IntrinsicCech.ScalarProjection.IntrinsicCechScalarProjection.map R S X Y f h U).f 0 := rfl
theorem row_one : (IntegralCechScalarProjection.map R S X Y f h U).f 1 = (IntrinsicCech.ScalarProjection.IntrinsicCechScalarProjection.map R S X Y f h U).f 1 := rfl
theorem row_two : (IntegralCechScalarProjection.map R S X Y f h U).f 2 = (IntrinsicCech.ScalarProjection.IntrinsicCechScalarProjection.map R S X Y f h U).f 2 := rfl

theorem iso_hom [Module.Flat R S] [IsSeparated X.hom]
    (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hU : ∀ i, IsAffineOpen (U i)) :
    (IntegralFirst.ThreeCechScalarBicomplex.IntegralFirstThreeCechScalarBicomplex.iso R S X Y f U hp hU).hom = IntegralCechScalarProjection.map R S X Y f hp.w U := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.ScalarProjection.IntegralCechScalarProjection
