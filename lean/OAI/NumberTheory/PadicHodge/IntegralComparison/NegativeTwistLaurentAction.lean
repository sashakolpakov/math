import OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistChartAction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntersectionPolynomial
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TwistFrameAction

/-! # Negative Twist Laurent Action -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistLaurentAction

noncomputable section

/-! On the full projective intersection, a native map between negative
twists acts by its homogeneous polynomial in the actual Laurent coordinates. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentPolynomialAction
  LaurentChartMultiplication Projective.SectionIntersections
  Projective.IntersectionPolynomial NegativeTwistChartAction

universe u

section Algebra

variable {σ : Type} [Fintype σ] (C : Type u) [CommRing C]

theorem ambient_reindex_polynomial_mul (m : ℕ) (d e : ℤ) (he : (m : ℤ) + d = e)
    {n : ℕ} (a : Fin (n + 1) → σ) (P : homogeneousSubmodule σ C m)
    (x : AddMonoidAlgebra C (AlgebraicGeometry.SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (AlgebraicGeometry.SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent a))) :
    LaurentPolynomialAction.ambient C e a (LaurentChartMultiplication.reindex C e a (AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom C a P.val * x)) =
      LaurentResiduePairing.polynomialMap σ C P.val * LaurentPolynomialAction.ambient C d a (LaurentChartMultiplication.reindex C d a x) := by
  subst e
  rw [LaurentChartMultiplication.reindex_polynomial_mul, LaurentPolynomialAction.ambient_polynomial]

end Algebra

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem native_factor_action (A B : ℕ) (hBA : B ≤ A) {n : ℕ}
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n)
    (f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (a.val 0).down (A + 1) ⟶
      AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (a.val 0).down (B + 1))
    (x : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (a.val 0).down (A + 1),
      AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val)) :
    (show Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val) from
      (AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.val (a.val 0).down (.negSucc B)).hom
        (f.app (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val) x)) =
    (Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a.val 0)).op
        (AlgebraicGeometry.SheafCohomology.Projective.ChartPolynomialMap.Dimension.projectiveChartPolynomialMap (R := R) (a.val 0).down
          (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) (a.val 0).down
            (A + 1) (B + 1) (Nat.add_le_add_right hBA 1) f).val) *
      (show Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val) from
        (AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.val (a.val 0).down (.negSucc A)).hom x) := by
  have h := Intrinsic.TwistFrameAction.factor_action (a.val 0).down (.negSucc A) (.negSucc B) a.val f x
  have hc : AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates.overFrameMapCoefficient (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (a.val 0).down)
      (Intrinsic.TwistFrameAction.frame (R := R) (a.val 0).down (a.val 0).down (.negSucc A))
      (Intrinsic.TwistFrameAction.frame (R := R) (a.val 0).down (a.val 0).down (.negSucc B)) f =
        AlgebraicGeometry.SheafCohomology.Projective.ChartPolynomialMap.Dimension.projectiveChartPolynomialMap (R := R) (a.val 0).down
          (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) (a.val 0).down
            (A + 1) (B + 1) (Nat.add_le_add_right hBA 1) f).val :=
    NegativeTwistChartAction.mapCoefficient_eq_polynomial (a.val 0).down (A + 1) (B + 1) (Nat.add_le_add_right hBA 1) f
  exact h.trans (congrArg (fun c : Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (a.val 0).down) =>
    (Proj (homogeneousSubmodule σ R)).presheaf.map
      (homOfLE (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a.val 0)).op c *
      (show Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val) from
        (AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.val (a.val 0).down (.negSucc A)).hom x)) hc)

theorem native_laurent_action (A B : ℕ) (hBA : B ≤ A) {n : ℕ}
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n)
    (f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (a.val 0).down (A + 1) ⟶
      AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (a.val 0).down (B + 1))
    (x : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (a.val 0).down (A + 1),
      AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val)) :
    LaurentPolynomialAction.ambient Γ(Spec (CommRingCat.of R), ⊤) (.negSucc B) (fun k => (a.val k).down)
      (Projective.SectionIntersections.coordinates (a.val 0).down (.negSucc B) a (f.app (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val) x)) =
    LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤)
        (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) (a.val 0).down
          (A + 1) (B + 1) (Nat.add_le_add_right hBA 1) f).val *
      LaurentPolynomialAction.ambient Γ(Spec (CommRingCat.of R), ⊤) (.negSucc A) (fun k => (a.val k).down)
        (Projective.SectionIntersections.coordinates (a.val 0).down (.negSucc A) a x) := by
  let P := AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) (a.val 0).down
    (A + 1) (B + 1) (Nat.add_le_add_right hBA 1) f
  let z : Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val) :=
    (AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.val (a.val 0).down (.negSucc A)).hom x
  have hr := congrArg (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a.val)
    (native_factor_action A B hBA a f x)
  rw [map_mul] at hr
  change AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a.val
      ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.val (a.val 0).down (.negSucc B)).hom
        (f.app (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val) x)) =
    AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartFrameCoefficient.MvPolynomial.coordinateChartCoefficientRingHom (R := R) a.val
      (AlgebraicGeometry.SheafCohomology.Projective.ChartPolynomialMap.Dimension.projectiveChartPolynomialMap (R := R) (a.val 0).down P.val) *
        AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a.val z at hr
  rw [Projective.IntersectionPolynomial.polynomial_restriction a ((A + 1) - (B + 1)) P] at hr
  have ht := congrArg (fun y => LaurentPolynomialAction.ambient Γ(Spec (CommRingCat.of R), ⊤) (.negSucc B)
    (fun k => (a.val k).down)
    (LaurentChartMultiplication.reindex Γ(Spec (CommRingCat.of R), ⊤) (.negSucc B) (fun k => (a.val k).down) y)) hr
  exact ht.trans (ambient_reindex_polynomial_mul Γ(Spec (CommRingCat.of R), ⊤)
    ((A + 1) - (B + 1)) (.negSucc A) (.negSucc B) (by omega)
    (fun k => (a.val k).down) P
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentRingEquiv (R := R) a.val z))

set_option backward.isDefEq.respectTransparency true in
attribute [local irreducible] AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials in
theorem native_laurent_action_at_chart (j : σ) (A B : ℕ) (hBA : B ≤ A) {n : ℕ}
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) (hj : j = (a.val 0).down)
    (f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (A + 1) ⟶
      AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (B + 1))
    (x : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (A + 1),
      AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val)) :
    LaurentPolynomialAction.ambient Γ(Spec (CommRingCat.of R), ⊤) (.negSucc B) (fun k => (a.val k).down)
      (Projective.SectionIntersections.coordinates j (.negSucc B) a (f.app (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val) x)) =
    LaurentResiduePairing.polynomialMap σ Γ(Spec (CommRingCat.of R), ⊤)
        (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) j
          (A + 1) (B + 1) (Nat.add_le_add_right hBA 1) f).val *
      LaurentPolynomialAction.ambient Γ(Spec (CommRingCat.of R), ⊤) (.negSucc A) (fun k => (a.val k).down)
        (Projective.SectionIntersections.coordinates j (.negSucc A) a x) := by
  subst j
  exact native_laurent_action A B hBA a f x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistLaurentAction
