import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Cohomology

/-! # Serre Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SerreComplex

noncomputable section

/-! The native residue trace identifies cohomology of the Hom complex of
an actual negative-twist resolution with the dual of complementary Čech
cohomology. Coefficients may be self-injective Artinian rings. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R]

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Duality

theorem coefficient_injective [Module.Injective R R] :
    Module.Injective (TopTracePairing.coefficientRing R) (TopTracePairing.coefficientRing R) := by
  let e : R ≃+* TopTracePairing.coefficientRing R :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  exact Module.Injective.of_ringEquiv e e.toSemilinearEquiv

variable [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

def homologyIso
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) (B : ℕ) (hB : 0 < B) (n : ℕ) (hn : Fintype.card σ = n + 2)
    (d : ℕ) (hd : d ≤ n + 1) :
    (ProjectiveResolution.Duality.homComplex M j B n hn).homology d ≅
      AddCommGrpCat.of (Module.Dual (TopTracePairing.coefficientRing R)
        ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) M
          (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology (n + 1 - d))) := by
  letI : Module.Injective (TopTracePairing.coefficientRing R) (TopTracePairing.coefficientRing R) := coefficient_injective
  exact ProjectiveResolution.Duality.homologyIso M j B n hn d ≪≫
    (forget₂ (ModuleCat.{u} (TopTracePairing.coefficientRing R)) AddCommGrpCat).mapIso
      ((ExactModuleDualFunctor.functor (TopTracePairing.coefficientRing R)).mapIso
        (ProjectiveResolution.Cohomology.comparisonIso M j B hB n hn d hd).op.symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SerreComplex
