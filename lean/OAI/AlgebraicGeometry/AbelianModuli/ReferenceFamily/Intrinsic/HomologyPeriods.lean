import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticePeriodEvaluation
import OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Homology Periods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods

noncomputable section

/-! Recover the actual degree-one homology marking from the proved
native singular-period comparison and universal-coefficient evaluation.
The construction is characterized by its pairing with every H1 class. -/

open OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient

section Dual

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V] [Module.Finite F V]
  [AddCommGroup W] [Module F W] [Module.Finite F W]

def fromDualEquiv (e : Module.Dual F W ≃ₗ[F] Module.Dual F V) : V ≃ₗ[F] W :=
  (Module.evalEquiv F V).trans (e.dualMap.trans (Module.evalEquiv F W).symm)

theorem fromDualEquiv_pairing (e : Module.Dual F W ≃ₗ[F] Module.Dual F V)
    (v : V) (φ : Module.Dual F W) : φ (fromDualEquiv e v) = e φ v := by
  have h := congrArg (fun f : Module.Dual F (Module.Dual F W) => f φ)
    ((Module.evalEquiv F W).apply_symm_apply (e.dualMap (Module.evalEquiv F V v)))
  exact h

end Dual

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

def nativeH1Periods : A.variety.rationalCohomology 1 ≃ₗ[ℚ]
    Module.Dual ℚ (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :=
  (AlgebraicTopology.Cohomology.Singular.Homotopy.singularCohomologyIsoOfHomotopyEquiv (ModuleCat.of ℚ ℚ)
    (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Torsion.IntrinsicTorsion.e06Input A).toHomotopyEquiv 1).toLinearEquiv.trans
      (LatticePeriodEvaluation.LatticeCharacters.singularH1LatticeDualEquiv (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A))

abbrev rationalHomologyOne := (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (Betti.Scheme.schemePointSpace A.toOver)).homology 1

instance nativeH1_finite : Module.Finite ℚ (A.variety.rationalCohomology 1) :=
  Module.Finite.of_injective (nativeH1Periods A).toLinearMap (nativeH1Periods A).injective

instance rationalHomologyOne_finite : Module.Finite ℚ (rationalHomologyOne A) := by
  let e := AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ) (Betti.Scheme.schemePointSpace A.toOver) 1
  let : Module.Finite ℚ (Module.Dual ℚ (rationalHomologyOne A)) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  exact (Module.finite_dual_iff ℚ).mp inferInstance

/-- The native rational period span identifies with actual singular H1
by dualizing its constructed period pairing. -/
def nativeHomologyPeriods : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A ≃ₗ[ℚ] rationalHomologyOne A :=
  fromDualEquiv ((AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ)
    (Betti.Scheme.schemePointSpace A.toOver) 1).symm.trans (nativeH1Periods A))

theorem nativeHomologyPeriods_pairing (v : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)
    (c : A.variety.rationalCohomology 1) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace A.toOver) 1 c
      (nativeHomologyPeriods A v) = nativeH1Periods A c v := by
  have h := fromDualEquiv_pairing
    ((AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ) (Betti.Scheme.schemePointSpace A.toOver) 1).symm.trans
      (nativeH1Periods A)) v
    (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ) (Betti.Scheme.schemePointSpace A.toOver) 1 c)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  rw [AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv_apply] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods
