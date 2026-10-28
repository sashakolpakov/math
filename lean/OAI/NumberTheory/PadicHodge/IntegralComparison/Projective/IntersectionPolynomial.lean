import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionIntersections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ChartPolynomialMap

/-! # Intersection Polynomial -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntersectionPolynomial

noncomputable section

/-! Dehomogenization of a homogeneous polynomial on an arbitrary ordered
projective intersection agrees with restriction from its first chart. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial

open OAI.AlgebraicGeometry.SheafCohomology.Projective.ChartPolynomialMap.Dimension OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentChartMultiplication
  SectionIntersections

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem section_polynomial_chart (j : σ) (m : ℕ)
    (s : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m, ⊤)) {n : ℕ}
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.val
      ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.val j (m : ℤ)).hom
        ((AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m).presheaf.map
          (homOfLE (show AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val ≤ ⊤ from le_top)).op s)) =
    AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (CommRingCat.of R), ⊤) (fun k => (a.val k).down)
      (AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j m s).val := by
  apply (LaurentChartMultiplication.reindex Γ(Spec (CommRingCat.of R), ⊤) (m : ℤ) (fun k => (a.val k).down)).injective
  change SectionIntersections.sectionCoordinates (R := R) j m s a = _
  rw [SectionIntersections.sectionCoordinates_expansion, AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartHomogeneous.MvPolynomial.polynomialChartRingHom_homogeneous, map_sum]
  unfold SectionIntersections.expansion
  apply Finset.sum_congr rfl
  intro e _
  rw [LaurentChartMultiplication.reindex_single, Equiv.apply_symm_apply]

theorem chartCoefficient (j : σ) (m : ℕ)
    (s : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m, ⊤)) {n : ℕ}
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (CommRingCat.of R), ⊤) (fun k => (a.val k).down)
      (AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j m s).val =
    AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartFrameCoefficient.MvPolynomial.coordinateChartCoefficientRingHom (R := R) a.val
      (AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationCoefficient (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)
        (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) (a.val 0).down)
        (AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame (R := R) (a.val 0).down j m) s) := by
  rw [← section_polynomial_chart j m s a, AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartFrameCoefficient.MvPolynomial.coordinateTwistBaseCechFactor_globalCoefficient]
  rfl

theorem polynomial_restriction {n : ℕ}
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) (m : ℕ)
    (P : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m) :
    AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartFrameCoefficient.MvPolynomial.coordinateChartCoefficientRingHom (R := R) a.val
      (AlgebraicGeometry.SheafCohomology.Projective.ChartPolynomialMap.Dimension.projectiveChartPolynomialMap (R := R) (a.val 0).down P.val) =
    AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (CommRingCat.of R), ⊤) (fun k => (a.val k).down) P.val := by
  obtain ⟨s, rfl⟩ :=
    (AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) (a.val 0).down m).surjective P
  rw [AlgebraicGeometry.SheafCohomology.Projective.ChartPolynomialMap.Dimension.projectiveChartPolynomialMap_section]
  exact (chartCoefficient (a.val 0).down m s a).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntersectionPolynomial
