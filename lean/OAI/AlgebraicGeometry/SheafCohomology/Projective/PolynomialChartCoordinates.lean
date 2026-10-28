import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroPolynomialChart
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials

/-! # Polynomial Chart Coordinates -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartCoordinates

noncomputable section

open _root_.MvPolynomial

/-! The projective polynomial-section equivalence has the canonical dehomogenization formula on charts. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateTwistGlobalSections_polynomial_chart (j : σ) (n : ℕ)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n, ⊤))
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0) :
    StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.val
      ((TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.val j (n : ℤ)).hom
        ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
          (homOfLE (show (∏ᶜ fun k : Fin 1 => StandardCech.MvPolynomial.coordinateOpenCover (R := R) (a.val k)) ≤ ⊤
            from le_top)).op x)) =
      PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (CommRingCat.of R), ⊤) (fun k => (a.val k).down)
        (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j n x).val := by
  let z := PolynomialSections.MvPolynomial.directCoordinateTwistGlobalSectionsLaurentEquiv (R := R) j n x
  have hc := LaurentZeroPolynomialChart.MvPolynomial.laurentZeroCyclesPolynomial_chart j n z a
  have hs := LaurentCoordinates.MvPolynomial.directCoordinateTwistGlobalSectionsLaurentEquiv_component (R := R) j n x a
  change LaurentCoordinates.MvPolynomial.homogeneousLaurentZeroComponent (n : ℤ) z a = _ at hs
  rw [hs] at hc
  let e := AddMonoidAlgebra.mapDomainLinearEquiv Γ(Spec (CommRingCat.of R), ⊤)
    Γ(Spec (CommRingCat.of R), ⊤)
    (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv (fun k => (a.val k).down) (n : ℤ))
  change e.symm (e _) = _ at hc
  rw [e.symm_apply_apply] at hc
  exact hc

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartCoordinates
