import OAI.NumberTheory.PadicHodge.GeometricComparison.GlobalDeRhamCoordinate
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarFiltration

/-! # Global Filtered Scalar Extension -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.GlobalFilteredScalarExtension.GlobalDeRhamScalarExtension

noncomputable section

/-! The actual global de Rham scalar equivalence preserves every original native Hodge filtration step. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hcover : iSup U = ⊤)
  (S : Type) [CommRing S] [Algebra R S] [Algebra ℚ S] [Module.Flat R S]
  (Y : Over (Spec (CommRingCat.of S))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))

theorem equiv_filtration (n : ℕ) (r : ℤ) :
    ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R X n r).baseChange S).map
      (GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension.equiv R X U hU hcover S Y f hp n).toLinearMap = AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration S Y n r := by
  let : IsSeparated Y.hom := Affine.BaseChangeCover.AffineBaseChangeCover.separated (algebraMap R S) X Y f hp
  let hV := fun i => Affine.BaseChangeCover.AffineBaseChangeCover.affine (algebraMap R S) X Y f hp (U i) (hU i)
  let hVcover := Affine.BaseChangeCover.AffineBaseChangeCover.cover X Y f U hcover
  exact ScalarEquivTransportNaturality.FilteredBaseChangeTransport.filtration S (GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension.coordinateEquiv R X U hU hcover n)
    (IntrinsicCech.ScalarTotal.IntrinsicCechScalarTotal.cohomologyEquiv R S X Y f U hp hU (n : ℤ))
    (GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension.coordinateEquiv S Y (fun i => f ⁻¹ᵁ U i) hV hVcover n)
    (FlatFiltered.FlatFilteredTotalCohomology.filtration (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U) (n : ℤ) r)
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R X n r)
    (FlatFiltered.FlatFilteredTotalCohomology.filtration (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex S Y (fun i => f ⁻¹ᵁ U i)) (n : ℤ) r)
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration S Y n r)
    (IntrinsicCech.Coordinate.IntrinsicCechCoordinateHodge.equiv_filtration R X U hU hcover n r)
    (IntrinsicCech.ScalarFiltration.IntrinsicCechScalarTotal.cohomologyEquiv_filtration R S X Y f U hp hU (n : ℤ) r)
    (IntrinsicCech.Coordinate.IntrinsicCechCoordinateHodge.equiv_filtration S Y (fun i => f ⁻¹ᵁ U i) hV hVcover n r)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.GlobalFilteredScalarExtension.GlobalDeRhamScalarExtension
