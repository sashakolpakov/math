import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineCechCoordinateUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.TruncatedSections
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.BaseChangeCover
import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarEquivTransportNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Coordinate

/-! # Global De Rham Coordinate -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension

noncomputable section

/-! Flat scalar extension of the original global derived de Rham cohomology, constructed from an actual finite affine cover. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hcover : iSup U = ⊤)

def coordinateEquiv (n : ℕ) : (IntrinsicCech.ScalarTotal.IntrinsicCechScalarTotal.complex R X U).homology (n : ℤ) ≃ₗ[R]
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X n :=
  IntrinsicCech.Coordinate.IntrinsicCechCoordinateHodge.equiv R X U hU hcover n

variable (S : Type) [CommRing S] [Algebra R S] [Algebra ℚ S] [Module.Flat R S]
  (Y : Over (Spec (CommRingCat.of S))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))

def equiv (n : ℕ) : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X n ≃ₗ[S] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology S Y n := by
  letI : IsSeparated Y.hom := Affine.BaseChangeCover.AffineBaseChangeCover.separated (algebraMap R S) X Y f hp
  exact ScalarEquivTransportNaturality.FilteredBaseChangeTransport.equiv S (coordinateEquiv R X U hU hcover n)
    (IntrinsicCech.ScalarTotal.IntrinsicCechScalarTotal.cohomologyEquiv R S X Y f U hp hU (n : ℤ))
    (coordinateEquiv S Y (fun i => f ⁻¹ᵁ U i)
      (fun i => Affine.BaseChangeCover.AffineBaseChangeCover.affine (algebraMap R S) X Y f hp (U i) (hU i))
      (Affine.BaseChangeCover.AffineBaseChangeCover.cover X Y f U hcover) n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension
