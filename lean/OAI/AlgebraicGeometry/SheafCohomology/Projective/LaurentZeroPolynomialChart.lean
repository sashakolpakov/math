import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroComponentExpansion
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartHomogeneous

/-! # Laurent Zero Polynomial Chart -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroPolynomialChart

noncomputable section

/-! Dehomogenization of the global polynomial equals the local Laurent coordinate of a zero cycle. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry
universe u
namespace MvPolynomial
open _root_.MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

theorem laurentZeroCyclesPolynomial_coefficients (j : σ) (n : ℕ)
    (z : LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) (n : ℤ)) :
    NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv Γ(Spec (CommRingCat.of R), ⊤) n
      (NonnegativeLaurentPolynomials.MvPolynomial.laurentZeroCyclesEquivPolynomials R j n z) =
        LaurentZeroCoefficients.MvPolynomial.laurentZeroCoefficients (R := R) (n : ℤ) j z :=
  (NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv Γ(Spec (CommRingCat.of R), ⊤) n).apply_symm_apply _

theorem laurentZeroCyclesPolynomial_chart (j : σ) (n : ℕ)
    (z : LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) (n : ℤ))
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0) :
    (AddMonoidAlgebra.mapDomainLinearEquiv Γ(Spec (CommRingCat.of R), ⊤)
      Γ(Spec (CommRingCat.of R), ⊤)
      (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv (fun k => (a.val k).down) (n : ℤ)).symm)
        (LaurentCoordinates.MvPolynomial.homogeneousLaurentZeroComponent (n : ℤ) z a) =
      PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (CommRingCat.of R), ⊤) (fun k => (a.val k).down)
        (NonnegativeLaurentPolynomials.MvPolynomial.laurentZeroCyclesEquivPolynomials R j n z).val := by
  rw [LaurentZeroComponentExpansion.MvPolynomial.laurentZeroComponent_eq_sum n j z a, map_sum, PolynomialChartHomogeneous.MvPolynomial.polynomialChartRingHom_homogeneous]
  apply Finset.sum_congr rfl
  intro e _
  rw [AddMonoidAlgebra.mapDomainLinearEquiv_single,
    laurentZeroCyclesPolynomial_coefficients]

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroPolynomialChart
