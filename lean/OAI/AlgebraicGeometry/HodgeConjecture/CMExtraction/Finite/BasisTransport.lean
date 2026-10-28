import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.TestTransport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.RationalSubstitution
import OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex

/-! # Basis Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.BasisTransport.Test

noncomputable section

/-! Finite-test transport for the selected rational position basis,
without replacing that basis by the integral-basis construction. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.TotallyRealData OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization

def reindexFiniteTest {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz J :=
  ⟨φ.val ∘ RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm,
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr
      ⟨((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mp φ.property).1.comp_continuous
          (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm).continuous,
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport φ).comp_homeomorph (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm)⟩⟩

theorem reindexFiniteTest_rational {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : J → ℚ) :
    (reindexFiniteTest e φ).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x) =
      φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (fun i => x (e i))) := rfl

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H K)

def transportBasisTest (p : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m) ≃ₗ[ℚ] (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℚ))
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m) :=
  TestTransport.transportFiniteTest A
    (RationalSubstitution.TestTransport.finiteRationalPullback ((RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition.rationalPositionCoordinates A).symm.trans p) φ)

theorem transportBasisTest_rational_value
    (p : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m) ≃ₗ[ℚ] (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℚ))
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F (3 * m) (transportBasisTest A p φ) (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (p x)) := by
  rw [transportBasisTest, TestTransport.transportFiniteTest_rational_value, RationalSubstitution.TestTransport.finiteRationalPullback_rational]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.BasisTransport.Test
