import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ComplexPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CovectorCup

/-! # Covector Periods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CovectorPeriods

noncomputable section

/-! Identity covectors of rational H1 classes evaluate on actual
rational periods by the original singular period comparison. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ComplexPeriods.IntrinsicComplexPeriods

theorem complexPeriods_covector (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : A.variety.analyticModel [⋀^Fin 1]→L[ℝ] ℂ) (ℓ : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    ComplexPeriods.IntrinsicComplexPeriods.complexPeriods A (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A 1 a) ℓ =
      a (fun _ => (ℓ : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) :=
  ComplexPeriods.IntrinsicComplexPeriods.complexPeriods_invariantForm A a ℓ

def nativeH1Covector (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (c : A.variety.rationalCohomology 1) :
    A.variety.analyticModel [⋀^Fin 1]→L[ℝ] ℂ :=
  (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A 1).symm
    (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace A.toOver) 1 c)

theorem nativeH1Covector_lattice (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (c : A.variety.rationalCohomology 1) (ℓ : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    nativeH1Covector A c (fun _ => (ℓ : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) =
      (HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A c (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ) : ℂ) := by
  have h := complexPeriods_covector A (nativeH1Covector A c) ℓ
  have he : AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A 1 (nativeH1Covector A c) =
      AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace A.toOver) 1 c :=
    (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A 1).apply_symm_apply _
  exact h.symm.trans ((congrArg (fun a => ComplexPeriods.IntrinsicComplexPeriods.complexPeriods A a ℓ) he).trans
    (ComplexPeriods.IntrinsicComplexPeriods.complexPeriods_rationalToComplex A c ℓ))

def oneCovectorLinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E [⋀^Fin 1]→L[ℝ] ℂ) : E →ₗ[ℝ] ℂ :=
  (MultilinearMap.ofSubsingleton ℝ E ℂ (0 : Fin 1)).symm
    a.toContinuousMultilinearMap.toMultilinearMap

theorem nativeH1Covector_period (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (c : A.variety.rationalCohomology 1) (v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    nativeH1Covector A c (fun _ => v.val) = (HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A c v : ℂ) := by
  let f : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] ℂ :=
    ((oneCovectorLinear (nativeH1Covector A c)).restrictScalars ℚ).comp (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A).subtype
  let g : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] ℂ :=
    (Algebra.linearMap ℚ ℂ).comp (HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A c)
  have he : f = g := by
    apply LatticePeriodEvaluation.LatticeCharacters.characterRestriction_injective (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
    ext ℓ
    exact nativeH1Covector_lattice A c ℓ
  exact DFunLike.congr_fun he v

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CovectorPeriods
