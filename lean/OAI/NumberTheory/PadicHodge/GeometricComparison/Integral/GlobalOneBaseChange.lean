import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechScalarTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.DeRhamOneCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.BaseChangeCover
import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarEquivTransportNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineCover

/-! # Global One Base Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.GlobalOneBaseChange.IntegralGlobalHOneBaseChange

noncomputable section

/-! Flat scalar extension of the original native global de Rham H-one over flat integer algebras. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open scoped TensorProduct

variable (R : Type) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)

def coordinateEquiv : (IntegralFirst.ThreeCechScalarTotal.IntegralFirstThreeCechScalarTotal.complex R X U).homology 1 ≃ₗ[R]
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X 1 :=
  (HomologicalComplex.homologyMapIso (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.totalIso R X U hU) 1).toLinearEquiv.trans
    (DeRhamOneCech.IntegralDeRhamHOneCech.equiv R X U hU hcover)

variable (S : Type) [CommRing S] [Algebra R S] [Module.Flat R S] [Module.Flat ℤ S]
  (Y : Over (Spec (CommRingCat.of S))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))

def equiv : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X 1 ≃ₗ[S] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology S Y 1 := by
  letI : IsSeparated Y.hom := Affine.BaseChangeCover.AffineBaseChangeCover.separated (algebraMap R S) X Y f hp
  exact ScalarEquivTransportNaturality.FilteredBaseChangeTransport.equiv S (coordinateEquiv R X U hU hcover)
    (IntegralFirst.ThreeCechScalarTotal.IntegralFirstThreeCechScalarTotal.cohomologyEquiv R S X Y f U hp hU 1)
    (coordinateEquiv S Y (fun i => f ⁻¹ᵁ U i)
      (fun i => Affine.BaseChangeCover.AffineBaseChangeCover.affine (algebraMap R S) X Y f hp (U i) (hU i))
      (Affine.BaseChangeCover.AffineBaseChangeCover.cover X Y f U hcover))

def quasiCompactEquiv [QuasiCompact X.hom] :
    S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X 1 ≃ₗ[S] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology S Y 1 :=
  equiv R X (GeometricComparison.Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens R X)
    (GeometricComparison.Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_affine R X)
    (GeometricComparison.Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_cover R X) S Y f hp

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.GlobalOneBaseChange.IntegralGlobalHOneBaseChange
