import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ChartAlgebra
import OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.CoordinateDifferentials
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorCoordinates
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Differential Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.DifferentialBasis

noncomputable section

/-! Differential frames on the actual standard projective charts, with
the original Cohomology structural algebra and literal coordinate functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Finite σ]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev ring (i : σ) := Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)

def basis (i : σ) :
    letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    Module.Basis {j : σ // j ≠ i} (ring (R := R) i) Ω[ring (R := R) i⁄R] := by
  letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  exact Polynomial.CoordinateDifferentials.basis (ChartAlgebra.equiv (R := R) i)

omit [Finite σ] in
theorem basis_apply (i : σ) (j : {j : σ // j ≠ i}) :
    letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    basis (R := R) i j = KaehlerDifferential.D R (ring (R := R) i)
      (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j) := by
  let := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  rw [basis, Polynomial.CoordinateDifferentials.basis_apply,
    ChartAlgebra.equiv_symm_variable]

variable {n : ℕ}

def orderedBasis (i : Fin (n + 1)) :
    letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    Module.Basis (Fin n) (ring (R := R) i) Ω[ring (R := R) i⁄R] := by
  letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  exact (basis (R := R) i).reindex (finSuccAboveEquiv i).symm

theorem orderedBasis_apply (i : Fin (n + 1)) (j : Fin n) :
    letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    orderedBasis (R := R) i j = KaehlerDifferential.D R (ring (R := R) i)
      (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i (i.succAbove j)) := by
  let := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  rw [orderedBasis, Module.Basis.reindex_apply, Equiv.symm_symm, basis_apply]
  rfl

def topEquiv (i : Fin (n + 1)) :
    letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (⋀[ring (R := R) i]^n Ω[ring (R := R) i⁄R]) ≃ₗ[ring (R := R) i] ring (R := R) i := by
  letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  exact TopExteriorCoordinates.equiv (orderedBasis (R := R) i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.DifferentialBasis
