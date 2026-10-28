import OAI.AlgebraicGeometry.SheafCohomology.Projective.ZeroCyclesLinearSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights

/-! # Polynomial Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSections

noncomputable section

open _root_.MvPolynomial

/-! Direct polynomial coordinates of projective twist sections, using literal chart restrictions. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.ZeroCyclesLinearSections
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def homogeneousLaurentZeroKernelEquivCycles (j : σ) (d : ℤ) :
    ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).d 0 1).hom.ker ≃ₗ[
      Γ(Spec (CommRingCat.of R), ⊤)] LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) d := by
  have hd : ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).d 0 1).hom =
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential (R := R) (σ := σ) d 0).hom := by
    rw [TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d]
  exact LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hd)

def directCoordinateTwistGlobalSectionsLaurentEquiv (j : σ) (n : ℕ) :
    letI := BaseZeroSections.baseGlobalSectionsModule (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
    Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n, ⊤) ≃ₗ[
      Γ(Spec (CommRingCat.of R), ⊤)] LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) (n : ℤ) := by
  let M := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
  let π := MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  letI := BaseZeroSections.baseGlobalSectionsModule π M
  let e := TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso (R := R) j (n : ℤ) ≪≫
    TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplexIso (R := R) j (n : ℤ)
  exact (ZeroCyclesLinearSections.orderedBaseTopSectionsZeroCyclesLinearEquiv π M
    (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))).trans
      ((Cech.CochainZeroCycleMaps.Projective.linearZeroCyclesEquivOfIso e).trans
        (homogeneousLaurentZeroKernelEquivCycles (R := R) j (n : ℤ)))

omit [Fintype σ] in
theorem directCoordinateTwistGlobalSectionsLaurentEquiv_val (j : σ) (n : ℕ)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n, ⊤)) :
    (directCoordinateTwistGlobalSectionsLaurentEquiv (R := R) j n x).val =
      ((TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso (R := R) j (n : ℤ) ≪≫
        TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplexIso (R := R) j (n : ℤ)).hom.f 0)
        (BaseZeroCyclesSections.orderedBaseTopSectionsZeroCyclesAddEquiv
          (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
          (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
          (StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ)) x).val := rfl

def directCoordinateTwistGlobalSectionsPolynomialEquiv (j : σ) (n : ℕ) :
    letI := BaseZeroSections.baseGlobalSectionsModule (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
    Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n, ⊤) ≃ₗ[
      Γ(Spec (CommRingCat.of R), ⊤)] homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) n := by
  letI := BaseZeroSections.baseGlobalSectionsModule (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
  exact (directCoordinateTwistGlobalSectionsLaurentEquiv (R := R) j n).trans
    (NonnegativeLaurentPolynomials.MvPolynomial.laurentZeroCyclesEquivPolynomials R j n)

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSections
