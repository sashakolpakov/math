import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiber
import Mathlib.RingTheory.Smooth.Basic

/-! # Smooth -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.Smooth.BundleCycles

noncomputable section

/-! Laurent extension preserves formal smoothness over the original base. -/

theorem laurent_formallySmooth (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FormallySmooth A B] :
    Algebra.FormallySmooth A (LaurentPolynomial B) := by
  let : IsScalarTower A (Polynomial B) (LaurentPolynomial B) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change LaurentPolynomial.C (algebraMap A B a) =
      Polynomial.toLaurent (Polynomial.C (algebraMap A B a))
    exact (Polynomial.toLaurent_C _).symm
  let : Algebra.FormallySmooth A (Polynomial B) := Algebra.FormallySmooth.comp A B _
  let : Algebra.FormallySmooth (Polynomial B) (LaurentPolynomial B) :=
    Algebra.FormallySmooth.of_isLocalization (Submonoid.powers (Polynomial.X : Polynomial B))
  exact Algebra.FormallySmooth.comp A (Polynomial B) _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.Smooth.BundleCycles
