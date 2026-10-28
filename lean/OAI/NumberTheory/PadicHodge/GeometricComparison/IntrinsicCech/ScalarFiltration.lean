import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.FlatFiltered

/-! # Scalar Filtration -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarFiltration.IntrinsicCechScalarTotal

noncomputable section

/-! The actual Čech scalar comparison preserves every form-degree filtration image. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left) {ι : Type} [Finite ι] (U : ι → X.left.Opens)
  [Algebra ℚ R] [Algebra ℚ S] [Module.Flat R S] [IsSeparated X.hom]
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hU : ∀ i, IsAffineOpen (U i))

theorem cohomologyEquiv_filtration (n r : ℤ) :
    ((FlatFiltered.FlatFilteredTotalCohomology.filtration (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U) n r).baseChange S).map
      (ScalarTotal.IntrinsicCechScalarTotal.cohomologyEquiv R S X Y f U hp hU n).toLinearMap =
    FlatFiltered.FlatFilteredTotalCohomology.filtration (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex S Y (fun i => f ⁻¹ᵁ U i)) n r :=
  FlatFiltered.FlatFilteredTotalCohomology.filtration_eq (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U)
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex S Y (fun i => f ⁻¹ᵁ U i)) (ScalarBicomplex.IntrinsicCechScalarBicomplex.iso R S X Y f U hp hU) n r

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarFiltration.IntrinsicCechScalarTotal
