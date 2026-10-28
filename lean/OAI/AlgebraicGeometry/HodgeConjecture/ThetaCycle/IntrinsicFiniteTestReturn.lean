import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.BasisTransport
import OAI.RepresentationTheory.Theta.Adelic.CompactSupport

/-! # Intrinsic Finite Test Return -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicFiniteTestReturn.CM

noncomputable section

/-! Return native finite Schwartz inputs to rational source coordinates.
The construction uses actual compactly supported coset tests and preserves
every rational weight, including for noncanonical comparison coordinates. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.BasisTransport.Test

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W)

theorem exists_native_finite_test_return
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) :
    ∃ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A), ∀ x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m),
      φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A x)) =
        RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) := by
  let ψ := RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F (3 * m) f
  obtain ⟨M, hM, hp⟩ :=
    RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.finite_locallyConstant_lattice_period ψ.val ψ.property.1 ψ.property.2
  let q : ℚ := M
  have hq : q ≠ 0 := by change (M : ℚ) ≠ 0; exact_mod_cast hM.ne'
  have hqF : algebraMap ℚ F q ≠ 0 := (map_ne_zero (algebraMap ℚ F)).mpr hq
  have hpF : ∀ u ∈ RepresentationTheory.Weil.AdelicSplitting.FiniteLattices.Construction.finiteAdelicPositionLattice (algebraMap ℚ F q) hqF,
      ∀ x, ψ.val (u + x) = ψ.val x := by
    simpa only [q, map_natCast] using hp
  obtain ⟨s, hs⟩ := RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finite_function_coset_expansion ψ.val ψ.property.2
    (algebraMap ℚ F q) hqF hpF
  let a := fun c : RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.FinitePositionQuotient (ι := Fin (3 * m)) (algebraMap ℚ F q) hqF =>
    RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finitePositionQuotientRep (algebraMap ℚ F q) hqF c
  let T := fun c => RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest q hq
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A (a c)))
  refine ⟨∑ c ∈ s, ψ.val (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c)) • T c, fun x => ?_⟩
  change (∑ c ∈ s, ψ.val (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition (a c)) • T c).val
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A x)) = ψ.val (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, T, RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction.latticeCosetTest_apply,
    CMExtraction.PositionLattices.TestTransport.rationalPositionCoordinates_coset_value]
  exact (hs (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)).symm

def nativeFiniteTestReturn
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) :=
  (exists_native_finite_test_return A f).choose

theorem native_finite_test_return_value
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    (nativeFiniteTestReturn A f).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A x)) =
      RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) :=
  (exists_native_finite_test_return A f).choose_spec x

def nativeFiniteBasisReturn
    (p : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m) ≃ₗ[ℚ] (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℚ))
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) :=
  CMExtraction.Finite.RationalSubstitution.TestTransport.finiteRationalPullback (p.symm.trans (RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A))
    (nativeFiniteTestReturn A f)

theorem native_finite_basis_return_value
    (p : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m) ≃ₗ[ℚ] (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℚ))
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    (nativeFiniteBasisReturn A p f).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (p x)) =
      RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) := by
  rw [nativeFiniteBasisReturn, CMExtraction.Finite.RationalSubstitution.TestTransport.finiteRationalPullback_rational]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact native_finite_test_return_value A f x

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicFiniteTestReturn.CM
