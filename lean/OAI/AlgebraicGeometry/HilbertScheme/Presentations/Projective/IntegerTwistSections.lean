import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseZeroCycleSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCycleWeights

/-! # Integer Twist Sections -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IntegerTwistSections

noncomputable section

/-! The actual global sections of every integer projective twist are
the corresponding homogeneous Laurent zero cycles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open _root_.MvPolynomial

universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def integerLaurentZeroKernelEquivCycles (j : σ) (d : ℤ) :
    ((SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).d 0 1).hom.ker ≃ₗ[Γ(Spec (.of R), ⊤)]
      SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) d := by
  have hd : ((SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).d 0 1).hom =
      (SheafCohomology.Projective.LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential (R := R) (σ := σ) d 0).hom := by
    rw [SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d]
    rfl
  exact LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hd)

def integerTwistGlobalSectionsLaurentEquiv (j : σ) (d : ℤ) :
    letI := Module.compHom Γ(SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d, ⊤)
      (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)).appTop.hom
    Γ(SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d, ⊤) ≃ₗ[Γ(Spec (.of R), ⊤)]
      SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) d := by
  let M := SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d
  let π := SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  letI := Module.compHom Γ(M, ⊤) π.appTop.hom
  let e := SheafCohomology.Projective.TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso (R := R) j d ≪≫
    SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplexIso (R := R) j d
  exact (BaseZeroCycleSections.directOrderedSectionsZeroCyclesLinearEquiv π M
    (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))).trans
      ((SheafCohomology.Cech.CochainZeroCycleMaps.Projective.linearZeroCyclesEquivOfIso e).trans
        (integerLaurentZeroKernelEquivCycles (R := R) j d))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IntegerTwistSections
