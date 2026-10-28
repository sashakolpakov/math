import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechReindex
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ReferenceCechMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomotopyEquiv
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights

/-! # Laurent Complex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentComplex.Dolbeault

noncomputable section

/-! The original algebraic Cech complex is homotopy equivalent to its existing homogeneous Laurent model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechReindex _root_.MvPolynomial Scheme.Modules

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveAlgebraicCechULiftIso (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAlgebraicTwistCechComplex n j d ≅
      (cechComplexFunctor (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := ℂ) (σ := Fin (n + 1)))).obj
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf :=
  AdditiveCechReindex.additiveCechReindexIso (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d).val.presheaf
    (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n) (Equiv.ulift : ULift.{0} (Fin (n + 1)) ≃ Fin (n + 1))

def projectiveAlgebraicNativeBaseIso (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    ((SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of ℂ))).mapHomologicalComplex (.up ℕ)).obj
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1)))
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := ℂ))) ≅
      ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAlgebraicTwistCechComplex n j d :=
  SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1)))
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := ℂ)) ≪≫
      (projectiveAlgebraicCechULiftIso n j d).symm

abbrev projectiveAlgebraicLaurentCechComplex (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :=
  ((SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of ℂ))).mapHomologicalComplex (.up ℕ)).obj
    (SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := ℂ) j d)

def projectiveAlgebraicLaurentHomotopyEquiv (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    HomotopyEquiv (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAlgebraicTwistCechComplex n j d) (projectiveAlgebraicLaurentCechComplex n j d) :=
  (HomotopyEquiv.ofIso (projectiveAlgebraicNativeBaseIso n j d).symm).trans
    (((SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of ℂ))).mapHomotopyEquiv
      (SheafCohomology.Projective.BaseCechHomotopyEquiv.Scheme.Modules.baseCechOrderedHomotopyEquiv (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := Fin (n + 1)))
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := ℂ)))).trans
      (HomotopyEquiv.ofIso
        (((SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of ℂ))).mapHomologicalComplex (.up ℕ)).mapIso
          (SheafCohomology.Projective.TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso (R := ℂ) j d ≪≫
            SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplexIso (R := ℂ) j d))))

def projectiveLaurentOriginalComparison (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    projectiveAlgebraicLaurentCechComplex n j d ⟶
      (cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).obj (ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj :=
  (projectiveAlgebraicLaurentHomotopyEquiv n j d).inv ≫ ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap n j d

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentComplex.Dolbeault
