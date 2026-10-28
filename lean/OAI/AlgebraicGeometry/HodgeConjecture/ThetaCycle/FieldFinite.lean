import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.BasisTransport
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicAnalysis

/-! # Field Finite -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FieldFinite.CM

noncomputable section

/-! ThetaCycle: retain the original finite Schwartz input when passing to
the actual number-field restricted tensor model. Every rational weight
and the complete rational theta series are preserved in the chosen basis. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.Evaluation
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.BasisTransport.Test

def nativeRationalFiniteInput {I : Type} [Fintype I] (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I :=
  ⟨φ.val, (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr φ.property⟩

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W)
  {I : Type} [Fintype I] (e : I ≃ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)
  (p : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m) ≃ₗ[ℚ] (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℚ))

def sourceFieldFiniteInput (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m) :=
  CMExtraction.Finite.BasisTransport.Test.transportBasisTest A p (CMExtraction.Finite.BasisTransport.Test.reindexFiniteTest e (nativeRationalFiniteInput φ))

theorem source_field_finite_input_weight (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I) (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F (3 * m) (sourceFieldFiniteInput A e p φ)
        (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      φ.val (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.diagonal (fun i => p x (e i))) := by
  unfold sourceFieldFiniteInput
  rw [CMExtraction.Finite.BasisTransport.Test.transportBasisTest_rational_value, CMExtraction.Finite.BasisTransport.Test.reindexFiniteTest_rational]
  rfl

theorem source_field_finite_theta_series (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I)
    (Z : Matrix I I ℂ) (z : I → ℂ) :
    (∑' x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m),
      RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F (3 * m) (sourceFieldFiniteInput A e p φ)
          (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.kernel Z (fun i => p x (e i)) z) =
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta φ Z z := by
  simp only [source_field_finite_input_weight]
  let q : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m) ≃ₗ[ℚ] (I → ℚ) :=
    p.trans (LinearEquiv.funCongrLeft ℚ ℚ e)
  exact q.toEquiv.tsum_eq (fun x => φ.val (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.diagonal x) * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.kernel Z x z)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FieldFinite.CM
