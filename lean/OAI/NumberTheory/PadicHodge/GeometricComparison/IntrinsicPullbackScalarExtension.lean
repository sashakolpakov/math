import OAI.NumberTheory.PadicHodge.GeometricComparison.GlobalFilteredScalarExtension
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineCover

/-! # Intrinsic Pullback Scalar Extension -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPullbackScalarExtension.QuasiCompactFilteredBaseChange

/-! Native filtered de Rham base change for quasi-compact separated schemes over rational rings, using a constructed finite affine cover. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
  [Algebra R S] [Module.Flat R S]
  (X : Over (Spec (CommRingCat.of R))) [QuasiCompact X.hom] [IsSeparated X.hom]
  (Y : Over (Spec (CommRingCat.of S))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))

def equiv (n : ℕ) : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X n ≃ₗ[S] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology S Y n :=
  GlobalDeRhamCoordinate.GlobalDeRhamScalarExtension.equiv R X (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens R X)
    (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_affine R X)
    (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_cover R X) S Y f hp n

theorem equiv_filtration (n : ℕ) (r : ℤ) :
    ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R X n r).baseChange S).map (equiv R S X Y f hp n).toLinearMap =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration S Y n r :=
  GlobalFilteredScalarExtension.GlobalDeRhamScalarExtension.equiv_filtration R X (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens R X)
    (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_affine R X)
    (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_cover R X) S Y f hp n r

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPullbackScalarExtension.QuasiCompactFilteredBaseChange

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPullbackScalarExtension

/-! Filtered scalar extension on the chosen geometric pullback object itself. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
  [Algebra R S] [Module.Flat R S]
  (X : Over (Spec (CommRingCat.of R))) [QuasiCompact X.hom] [IsSeparated X.hom]

def equiv (n : ℕ) : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R X n ≃ₗ[S]
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology S ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj X) n :=
  QuasiCompactFilteredBaseChange.equiv R S X _
    (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (IsPullback.of_hasPullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S)))) n

theorem equiv_filtration (n : ℕ) (r : ℤ) :
    ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration R X n r).baseChange S).map (equiv R S X n).toLinearMap =
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration S
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj X) n r := by
  let Y : Over (Spec (CommRingCat.of S)) :=
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj X
  let f : Y.left ⟶ X.left := pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  have hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    IsPullback.of_hasPullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  exact QuasiCompactFilteredBaseChange.equiv_filtration R S X Y f hp n r

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPullbackScalarExtension

end

end OAI
