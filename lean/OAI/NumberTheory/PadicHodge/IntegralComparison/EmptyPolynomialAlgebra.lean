import Mathlib.RingTheory.Etale.Basic
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Empty Polynomial Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EmptyPolynomialAlgebra

noncomputable section

/-! An actual étale algebra is an étale chart with no polynomial variables. -/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

abbrev algebra : Algebra (MvPolynomial PEmpty.{u + 1} R) A :=
  (MvPolynomial.aeval (fun i : PEmpty.{u + 1} => i.elim) : MvPolynomial PEmpty.{u + 1} R →ₐ[R] A).toRingHom.toAlgebra

attribute [local instance] algebra

abbrev tower : IsScalarTower R (MvPolynomial PEmpty.{u + 1} R) A :=
  IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R A r = MvPolynomial.aeval (fun i : PEmpty.{u + 1} => i.elim) (MvPolynomial.C r)
    rw [MvPolynomial.aeval_C])

attribute [local instance] tower

theorem etale [Algebra.Etale R A] : Algebra.Etale (MvPolynomial PEmpty.{u + 1} R) A := by
  let : Algebra.Etale R (MvPolynomial PEmpty.{u + 1} R) :=
    Algebra.Etale.of_equiv (MvPolynomial.isEmptyAlgEquiv R PEmpty.{u + 1}).symm
  exact Algebra.Etale.of_restrictScalars R (MvPolynomial PEmpty.{u + 1} R) A

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EmptyPolynomialAlgebra
