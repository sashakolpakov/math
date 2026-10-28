import OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentChartMultiplication
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartCoordinates

/-! # Section Intersections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionIntersections

noncomputable section

/-! A global section of a positive projective twist has its same
homogeneous polynomial on every ordered affine intersection. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentPolynomialAction OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentChartMultiplication

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

def coordinates (j : σ) (d : ℤ) {n : ℕ}
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) n a.val ≃ₗ[
        Γ(Spec (CommRingCat.of R), ⊤)]
      AddMonoidAlgebra Γ(Spec (CommRingCat.of R), ⊤) (LaurentPolynomialAction.Allowed d (fun k => (a.val k).down)) :=
  (AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.val j d).toLinearEquiv.trans
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a.val d)

def sectionCoordinates (j : σ) (m : ℕ)
    (s : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m, ⊤)) {n : ℕ}
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    AddMonoidAlgebra Γ(Spec (CommRingCat.of R), ⊤) (LaurentPolynomialAction.Allowed (m : ℤ) (fun k => (a.val k).down)) :=
  coordinates j (m : ℤ) a
    ((AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m).presheaf.map
      (homOfLE (show AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val ≤ ⊤ from le_top)).op s)

def expansion (m : ℕ) (P : homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) m) {n : ℕ}
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    AddMonoidAlgebra Γ(Spec (CommRingCat.of R), ⊤) (LaurentPolynomialAction.Allowed (m : ℤ) (fun k => (a.val k).down)) :=
  ∑ e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ),
    AddMonoidAlgebra.single (AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed (fun k => (a.val k).down) m e)
      (AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv Γ(Spec (CommRingCat.of R), ⊤) m P e)

omit [Fintype σ] in
theorem sectionCoordinates_delete (j : σ) (m : ℕ)
    (s : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m, ⊤)) {n : ℕ}
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (k : Fin (n + 1)) :
    sectionCoordinates (R := R) j m s a =
      AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k.succ (m : ℤ)
        (sectionCoordinates (R := R) j m s (a.delete k.succ)) := by
  let M := AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m
  let y := M.presheaf.map
    (homOfLE (show AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) (a.delete k.succ).val ≤ ⊤ from le_top)).op s
  have hs : M.presheaf.map (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a k.succ).op y =
      M.presheaf.map (homOfLE (show AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val ≤ ⊤ from le_top)).op s := by
    dsimp only [y]
    rw [← M.presheaf.map_comp_apply]
    congr 1
  have hf := ConcreteCategory.congr_hom
    (AlgebraicGeometry.SheafCohomology.Projective.TwistCechFirstFrame.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit_naturality_delete_of_ne_zero
      (R := R) a k.succ (Fin.succ_ne_zero k) j (m : ℤ)) y
  change (AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.val j (m : ℤ)).hom
      (M.presheaf.map (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a k.succ).op y) =
    (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a k.succ).op
        ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) (a.delete k.succ).val j (m : ℤ)).hom y) at hf
  rw [hs] at hf
  change AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a.val (m : ℤ)
    ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.val j (m : ℤ)).hom
      (M.presheaf.map (homOfLE (show AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val ≤ ⊤ from le_top)).op s)) = _
  rw [hf]
  exact AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_naturality_delete_succ
    (R := R) a k (m : ℤ) _

theorem sectionCoordinates_expansion (j : σ) (m : ℕ)
    (s : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m, ⊤)) (n : ℕ)
    (a : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    sectionCoordinates (R := R) j m s a =
      expansion m (AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j m s) a := by
  induction n with
  | zero =>
    change LaurentChartMultiplication.reindex Γ(Spec (CommRingCat.of R), ⊤) (m : ℤ) (fun k => (a.val k).down)
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.val
        ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit (R := R) a.val j (m : ℤ)).hom
          ((AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m).presheaf.map
            (homOfLE (show AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.val ≤ ⊤ from le_top)).op s))) = _
    rw [AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartCoordinates.MvPolynomial.coordinateTwistGlobalSections_polynomial_chart, AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartHomogeneous.MvPolynomial.polynomialChartRingHom_homogeneous, map_sum]
    unfold expansion
    apply Finset.sum_congr rfl
    intro e _
    rw [LaurentChartMultiplication.reindex_single, Equiv.apply_symm_apply]
  | succ n ih =>
    rw [sectionCoordinates_delete j m s a (Fin.last n), ih (a.delete (Fin.last n).succ)]
    simp only [expansion, map_sum, AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateHomogeneousLaurentDeleteLinearMap_single]
    apply Finset.sum_congr rfl
    intro e _
    rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionIntersections
