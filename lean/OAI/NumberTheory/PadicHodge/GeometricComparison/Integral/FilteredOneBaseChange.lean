import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Coordinate
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechScalarFiltration

/-! # Filtered One Base Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FilteredOneBaseChange.IntegralGlobalHOneBaseChange

noncomputable section

/-! The actual global de Rham scalar equivalence preserves every original native Hodge filtration step. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hcover : iSup U = ⊤)
  (S : Type) [CommRing S] [Algebra R S] [Module.Flat ℤ S] [Module.Flat R S]
  (Y : Over (Spec (CommRingCat.of S))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))

theorem equiv_filtration (r : ℤ) :
    ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R X 1 r).baseChange S).map
      (GlobalOneBaseChange.IntegralGlobalHOneBaseChange.equiv R X U hU hcover S Y f hp).toLinearMap = AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration S Y 1 r := by
  let : IsSeparated Y.hom := Affine.BaseChangeCover.AffineBaseChangeCover.separated (algebraMap R S) X Y f hp
  let hV := fun i => Affine.BaseChangeCover.AffineBaseChangeCover.affine (algebraMap R S) X Y f hp (U i) (hU i)
  let hVcover := Affine.BaseChangeCover.AffineBaseChangeCover.cover X Y f U hcover
  exact ScalarEquivTransportNaturality.FilteredBaseChangeTransport.filtration S (GlobalOneBaseChange.IntegralGlobalHOneBaseChange.coordinateEquiv R X U hU hcover)
    (IntegralFirst.ThreeCechScalarTotal.IntegralFirstThreeCechScalarTotal.cohomologyEquiv R S X Y f U hp hU (1 : ℤ))
    (GlobalOneBaseChange.IntegralGlobalHOneBaseChange.coordinateEquiv S Y (fun i => f ⁻¹ᵁ U i) hV hVcover)
    (FlatFiltered.FlatFilteredTotalCohomology.filtration (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U) (1 : ℤ) r)
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R X 1 r)
    (FlatFiltered.FlatFilteredTotalCohomology.filtration (IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex S Y (fun i => f ⁻¹ᵁ U i)) (1 : ℤ) r)
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration S Y 1 r)
    (IntegralCech.Coordinate.IntegralCechCoordinateHodge.equiv_filtration R X U hU hcover r)
    (IntegralFirst.ThreeCechScalarFiltration.IntegralFirstThreeCechScalarTotal.cohomologyEquiv_filtration R S X Y f U hp hU (1 : ℤ) r)
    (IntegralCech.Coordinate.IntegralCechCoordinateHodge.equiv_filtration S Y (fun i => f ⁻¹ᵁ U i) hV hVcover r)

theorem quasiCompactEquiv_filtration [QuasiCompact X.hom] (r : ℤ) :
    ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R X 1 r).baseChange S).map
      (GlobalOneBaseChange.IntegralGlobalHOneBaseChange.quasiCompactEquiv R X S Y f hp).toLinearMap = AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration S Y 1 r :=
  equiv_filtration R X (GeometricComparison.Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens R X)
    (GeometricComparison.Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_affine R X)
    (GeometricComparison.Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_cover R X) S Y f hp r

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FilteredOneBaseChange.IntegralGlobalHOneBaseChange
