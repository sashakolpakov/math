import OAI.AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CochainZeroKernel
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSections

/-! # Degree Zero Polynomials -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! Actual global sections of a nonnegative projective twist are homogeneous polynomials. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def homogeneousLaurentHZeroLinearEquivCycles (j : σ) (d : ℤ) :
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homology 0 ≃ₗ[
      Γ(Spec (CommRingCat.of R), ⊤)] LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) d := by
  let K := TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d
  let e := CochainZeroKernel.cochainHZeroLinearEquivKernel K
  have hd : (K.d 0 1).hom =
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential (R := R) (σ := σ) d 0).hom := by
    dsimp only [K]
    rw [TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d]
    rfl
  exact e.trans (LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hd))

def coordinateTwistHZeroLinearEquivPolynomials (j : σ) (n : ℕ) :
    (OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
      (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology 0 ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
      homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) n :=
  (HomologicalComplex.homologyMapIso
    (TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso (R := R) j (n : ℤ) ≪≫
      TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplexIso (R := R) j (n : ℤ)) 0).toLinearEquiv.trans
    ((homogeneousLaurentHZeroLinearEquivCycles (R := R) j (n : ℤ)).trans
      (NonnegativeLaurentPolynomials.MvPolynomial.laurentZeroCyclesEquivPolynomials R j n))

def coordinateTwistGlobalSectionsLinearEquivPolynomials (j : σ) (n : ℕ) :
    let π := MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
    letI := BaseZeroSections.baseGlobalSectionsModule π M
    Γ(M, ⊤) ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
      homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) n :=
  PolynomialSections.MvPolynomial.directCoordinateTwistGlobalSectionsPolynomialEquiv (R := R) j n

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials.MvPolynomial
