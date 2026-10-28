import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.DifferentialBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactDifferentialBasis

/-! # Intrinsic Top Forms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicTopForms.Intrinsic

noncomputable section

/-! On the actual projective charts, native ordinary differential forms
are their Kähler exterior powers, and the top native form has its exact
coordinate trivialization over the original base ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.DifferentialBasis

universe u
variable {R : Type u} [CommRing R] {n : ℕ} (i : Fin (n + 1))

attribute [local instance] MvPolynomial.gradedAlgebra

def liftedBasis :
    letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    Module.Basis (ULift.{u} (Fin n)) (DifferentialBasis.ring (R := R) i) Ω[DifferentialBasis.ring (R := R) i⁄R] := by
  letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  exact (DifferentialBasis.orderedBasis (R := R) i).reindex Equiv.ulift.symm

def coordinate (j : ULift.{u} (Fin n)) : DifferentialBasis.ring (R := R) i :=
  AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i (i.succAbove j.down)

theorem liftedBasis_apply (j : ULift.{u} (Fin n)) :
    letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    liftedBasis (R := R) i j = KaehlerDifferential.D R (DifferentialBasis.ring (R := R) i) (coordinate i j) := by
  let := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  rw [liftedBasis, Module.Basis.reindex_apply]
  exact DifferentialBasis.orderedBasis_apply i j.down

def exteriorEquiv (d : ℕ) :
    letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (DifferentialBasis.ring (R := R) i) d ≃ₗ[DifferentialBasis.ring (R := R) i]
      ⋀[DifferentialBasis.ring (R := R) i]^d Ω[DifferentialBasis.ring (R := R) i⁄R] := by
  letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  exact ExactDifferentialBasis.exteriorEquiv R (DifferentialBasis.ring (R := R) i)
    (ULift.{u} (Fin n)) (coordinate i) d (liftedBasis i) (liftedBasis_apply i)

theorem exteriorEquiv_eq (d : ℕ) :
    letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (exteriorEquiv (R := R) i d).toLinearMap = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R (DifferentialBasis.ring (R := R) i) d := by
  let := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  exact ExactDifferentialBasis.exteriorEquiv_eq R (DifferentialBasis.ring (R := R) i)
    (ULift.{u} (Fin n)) (coordinate i) d (liftedBasis i) (liftedBasis_apply i)

def topEquiv :
    letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (DifferentialBasis.ring (R := R) i) n ≃ₗ[DifferentialBasis.ring (R := R) i] DifferentialBasis.ring (R := R) i := by
  letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  exact (exteriorEquiv (R := R) i n).trans (DifferentialBasis.topEquiv i)

def generator :
    letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (DifferentialBasis.ring (R := R) i) n := by
  letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  exact AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (DifferentialBasis.ring (R := R) i) 1
    (fun j => AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i (i.succAbove j))

theorem topEquiv_generator :
    letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    topEquiv (R := R) i (generator i) = 1 := by
  let := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  have he : exteriorEquiv (R := R) i n (generator i) =
      TopExteriorCoordinates.generator (DifferentialBasis.orderedBasis (R := R) i) := by
    change (exteriorEquiv (R := R) i n).toLinearMap (generator i) = _
    rw [exteriorEquiv_eq, generator, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol, one_smul]
    exact congrArg (exteriorPower.ιMulti (DifferentialBasis.ring (R := R) i) n)
      (funext (fun j => (DifferentialBasis.orderedBasis_apply i j).symm))
  change TopExteriorCoordinates.equiv (DifferentialBasis.orderedBasis (R := R) i)
    (exteriorEquiv (R := R) i n (generator i)) = 1
  rw [he]
  exact TopExteriorCoordinates.coordinate_generator _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicTopForms.Intrinsic
