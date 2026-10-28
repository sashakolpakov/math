import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PositionLattices
import OAI.RepresentationTheory.Theta.CosetTests
import OAI.RepresentationTheory.Weil.AdelicSplitting.CosetTestFamilies
import OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation

/-! # Test Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.TestTransport

noncomputable section

/-! Every rational finite Schwartz test has an actual restricted tensor
test over the number field with exactly the same rational weights in the
integral-basis position coordinates. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.CosetTestFamilies.Construction
open OAI.RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.TotallyRealData OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def finiteCosetTensor (q : F) (hq : q ≠ 0) (a : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N :=
  RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) (RepresentationTheory.Weil.AdelicSplitting.CosetTestFamilies.Construction.finiteCosetTest F N q hq a)
    (RepresentationTheory.Weil.AdelicSplitting.CosetTestFamilies.Construction.finiteCosetTest_eventually_vacuum F N q hq a)

theorem finiteCosetTensor_value (q : F) (hq : q ≠ 0)
    (a x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (finiteCosetTensor F N q hq a) x =
      RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionCosetIndicator q hq a x := by
  rw [finiteCosetTensor, RepresentationTheory.Theta.Adelic.ThetaEvaluation.finite_value_pure F N (fun _ => 0)]
  exact (RepresentationTheory.Weil.AdelicSplitting.FiniteLatticeFactors.Construction.finitePositionCosetIndicator_product F N q hq a x).symm

variable {F} {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H K)

theorem exists_finite_test_rational_values
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) :
    ∃ f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m),
      ∀ x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m),
        RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
          φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A x)) := by
  obtain ⟨n, hn, s, hs⟩ := RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.finiteSchwartz_coset_expansion_eq φ
  let q : ℚ := n
  have hq : q ≠ 0 := by change (n : ℚ) ≠ 0; exact_mod_cast hn.ne'
  let a := fun c => (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A).symm (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteQuotientRep q hq c)
  let coeff := fun c => φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteQuotientRep q hq c))
  let T := fun c => finiteCosetTensor F (3 * m) (algebraMap ℚ F q)
    ((map_ne_zero (algebraMap ℚ F)).mpr hq) (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c))
  have hT (c) (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
      RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F (3 * m) (T c) (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
        (RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteQuotientRep q hq c))).val
          (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A x)) := by
    dsimp only [T]
    rw [finiteCosetTensor_value, RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest_apply,
      ← PositionLattices.TestTransport.rationalPositionCoordinates_coset_value A q hq (a c) x]
    simp only [a, LinearEquiv.apply_symm_apply]
  refine ⟨∑ c ∈ s, coeff c • T c, fun x => ?_⟩
  have hx := congrArg (fun ψ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) =>
    ψ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A x))) hs
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, hT, smul_eq_mul]
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul] using hx.symm

def transportFiniteTest (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m) :=
  (exists_finite_test_rational_values A φ).choose

theorem transportFiniteTest_rational_value
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F (3 * m) (transportFiniteTest A φ) (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A x)) :=
  (exists_finite_test_rational_values A φ).choose_spec x

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.TestTransport
