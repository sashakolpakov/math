import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.PeriodDuality
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.RationalAlgebraic

/-! # Rational Periods -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.RationalPeriods.CM.Abelian

noncomputable section

/-! The rational H¹ comparison is evaluation on genuine lattice loops. -/

open _root_.CategoryTheory
open scoped TensorProduct

variable {U ι : Type} [AddCommGroup U] [Module ℚ U]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ U)
  (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (P : ComplexMultiplication.CM.Polarization.WeightOnePolarization H)
  (hRiemannProjectivity : ProjectiveTorusData.CM.Abelian.RiemannProjectivityInput)

local notation "D" => OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.ProjectivePeriodData.ofHodgeStructure b H P hRiemannProjectivity

/-- Polarization, lattice characters, and loop evaluation define this rational equivalence. -/
def polarizedRationalBettiEquiv : U ≃ₗ[ℚ]
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (D).periodTorus) 1 :=
  (PeriodDuality.CM.Abelian.polarizationDualEquiv H P).trans
    ((PeriodDuality.CM.Abelian.genericLatticeDualEquiv b H).trans (RationalAlgebraic.CM.Abelian.Algebraization.Characters.rationalPeriodEquiv D).symm)

theorem polarizedRationalBettiEquiv_period (u : U) (i : ι) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (D).periodTorus) 1
      (polarizedRationalBettiEquiv b H P hRiemannProjectivity u)
      (RationalAlgebraic.CM.Abelian.Algebraization.Loops.latticeHomology D ℚ (PeriodDuality.CM.Abelian.genericLatticeBasis b H i)) = P.form u (b i) := by
  let : Module.Finite ℚ U := H.finiteDimensional
  have h := (RationalAlgebraic.CM.Abelian.Algebraization.Characters.rationalPeriodEquiv D).apply_symm_apply
    (show (D).periodIntegerLattice →ₗ[ℤ] ℚ from
      PeriodDuality.CM.Abelian.genericLatticeDualEquiv b H (PeriodDuality.CM.Abelian.polarizationDualEquiv H P u))
  have hp := LinearMap.congr_fun h (PeriodDuality.CM.Abelian.genericLatticeBasis b H i)
  exact hp.trans ((PeriodDuality.CM.Abelian.genericLatticeDualEquiv_basis b H (PeriodDuality.CM.Abelian.polarizationDualEquiv H P u) i).trans
    (LinearMap.BilinForm.toDual_def P.nondegenerate))

theorem polarizedRationalBettiEquiv_covector (u : U) (i : ι) :
    RationalAlgebraic.CM.Abelian.Algebraization.Characters.rationalCovector D (polarizedRationalBettiEquiv b H P hRiemannProjectivity u)
      (ProjectiveTorusData.CM.Abelian.genericPeriodBasis b H i) = (P.form u (b i) : ℂ) := by
  have h := RationalAlgebraic.CM.Abelian.Algebraization.Characters.rationalCovector_period D
    (polarizedRationalBettiEquiv b H P hRiemannProjectivity u) (PeriodDuality.CM.Abelian.genericLatticeBasis b H i)
  rw [polarizedRationalBettiEquiv_period] at h
  have hb : (PeriodDuality.CM.Abelian.genericLatticeBasis b H i : ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H) = ProjectiveTorusData.CM.Abelian.genericPeriodBasis b H i :=
    (ProjectiveTorusData.CM.Abelian.genericPeriodBasis b H).restrictScalars_apply ℤ i
  exact (congrArg (fun v : ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H =>
    RationalAlgebraic.CM.Abelian.Algebraization.Characters.rationalCovector D (polarizedRationalBettiEquiv b H P hRiemannProjectivity u) v) hb).symm.trans h

def polarizedComplexCovectorEquiv : ComplexMultiplication.WeightOne.CM.Complexification U ≃ₗ[ℂ]
    (ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H →L[ℝ] ℂ) :=
  (LinearEquiv.baseChange ℚ ℂ _ _ (polarizedRationalBettiEquiv b H P hRiemannProjectivity)).trans
    (RationalAlgebraic.CM.Abelian.Algebraization.Rational.rationalComplexificationCovectors D)

theorem polarizedComplexCovectorEquiv_tmul (c : ℂ) (u : U) :
    polarizedComplexCovectorEquiv b H P hRiemannProjectivity (c ⊗ₜ[ℚ] u) =
      c • RationalAlgebraic.CM.Abelian.Algebraization.Characters.rationalCovector D (polarizedRationalBettiEquiv b H P hRiemannProjectivity u) := by
  change (AlgebraicBetti.CM.Abelian.Algebraization.Betti.invariantBettiH1Equiv D).symm
    (c • AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of (D).periodTorus) 1
      (polarizedRationalBettiEquiv b H P hRiemannProjectivity u)) = _
  exact (AlgebraicBetti.CM.Abelian.Algebraization.Betti.invariantBettiH1Equiv D).symm.map_smul c _

theorem polarizedComplexCovectorEquiv_basis (x : ComplexMultiplication.WeightOne.CM.Complexification U) (i : ι) :
    polarizedComplexCovectorEquiv b H P hRiemannProjectivity x (ProjectiveTorusData.CM.Abelian.genericPeriodBasis b H i) =
      P.form.baseChange ℂ x ((1 : ℂ) ⊗ₜ[ℚ] b i) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, add_apply, LinearMap.add_apply, hx, hy]
  | tmul c u =>
    rw [polarizedComplexCovectorEquiv_tmul]
    change c * RationalAlgebraic.CM.Abelian.Algebraization.Characters.rationalCovector D (polarizedRationalBettiEquiv b H P hRiemannProjectivity u)
      (ProjectiveTorusData.CM.Abelian.genericPeriodBasis b H i) = _
    rw [polarizedRationalBettiEquiv_covector, LinearMap.BilinForm.baseChange_tmul]
    change c * (P.form u (b i) : ℂ) = (P.form u (b i) : ℂ) * (c * 1)
    ring

/-- Equality is checked on the actual real basis, using the computed loop periods. -/
theorem polarizedComplexCovectorEquiv_eq (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    polarizedComplexCovectorEquiv b H P hRiemannProjectivity x = PeriodDuality.CM.Abelian.polarizedPeriodCovector P x := by
  apply ContinuousLinearMap.coe_injective
  apply (ProjectiveTorusData.CM.Abelian.genericPeriodBasis b H).ext
  intro i
  exact (polarizedComplexCovectorEquiv_basis b H P hRiemannProjectivity x i).trans
    (PeriodDuality.CM.Abelian.polarizedPeriodCovector_basis b P x i).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.RationalPeriods.CM.Abelian
