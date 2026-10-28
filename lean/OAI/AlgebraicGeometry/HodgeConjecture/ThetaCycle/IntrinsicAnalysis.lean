import OAI.RepresentationTheory.Theta.Kernel.Schwartz
import OAI.RepresentationTheory.Theta.Factorization
import OAI.Analysis.Theta.GaussianConvergence
import OAI.Analysis.Schwartz.TensorDecomposition
import OAI.RepresentationTheory.Theta.AdelicTopology

/-! # Intrinsic Analysis -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicAnalysis.CM

noncomputable section

/-! Discharge ThetaKernel's full analytic and finite-product prerequisites
using the native GaussianConvergence, DerivativeFactorization, and TensorDecomposition proofs. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open OAI.RepresentationTheory.Theta.Kernel.Schwartz

theorem nativeGaussianConvergenceInput (ι : Type*) [Fintype ι] : RepresentationTheory.Theta.Kernel.Analysis.GaussianConvergenceInput ι :=
  Analysis.Theta.GaussianConvergence.Construction.gaussian_theta_derivatives

theorem nativeDerivativeFactorizationInput (ι κ : Type*) [Fintype ι] [Fintype κ] : RepresentationTheory.Theta.Kernel.Factorization.DerivativeFactorizationInput ι κ :=
  RepresentationTheory.Theta.Factorization.Derivative.direct_sum_factorization

theorem c38_completed_eq {ι : Type*} [Fintype ι]
    (φ : RepresentationTheory.Theta.DerivativeFactorizationDefinitions.Input ι) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z = RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed φ Z := rfl

theorem finite_adeles_totally_disconnected : TotallyDisconnectedSpace RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := by
  let : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      TotallyDisconnectedSpace (v.adicCompletion ℚ) := fun v =>
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.symm.totallyDisconnectedSpace
  let f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf → (v : IsDedekindDomain.HeightOneSpectrum ℤ) → v.adicCompletion ℚ :=
    fun a v => a v
  have hf : Continuous f := RestrictedProduct.continuous_coe
  exact ⟨isTotallyDisconnected_of_image hf.continuousOn DFunLike.coe_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem nativeTensorDecompositionProductInput (ι κ : Type*) [Fintype ι] [Fintype κ] : RepresentationTheory.Theta.Kernel.Schwartz.ProductInput ι κ := by
  let : TotallyDisconnectedSpace RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := finite_adeles_totally_disconnected
  let : ∀ b : Bool, T2Space (RepresentationTheory.Theta.Kernel.Schwartz.BinaryBlock ι κ b) := fun b => by
    cases b <;> dsimp [RepresentationTheory.Theta.Kernel.Schwartz.BinaryBlock] <;> infer_instance
  let : ∀ b : Bool, LocallyCompactSpace (RepresentationTheory.Theta.Kernel.Schwartz.BinaryBlock ι κ b) := fun b => by
    cases b <;> dsimp [RepresentationTheory.Theta.Kernel.Schwartz.BinaryBlock]
    · exact Homeomorph.ulift.isOpenEmbedding.locallyCompactSpace
    · exact Homeomorph.ulift.isOpenEmbedding.locallyCompactSpace
  let : ∀ b : Bool, TotallyDisconnectedSpace (RepresentationTheory.Theta.Kernel.Schwartz.BinaryBlock ι κ b) := fun b => by
    cases b <;> dsimp [RepresentationTheory.Theta.Kernel.Schwartz.BinaryBlock]
    · exact Homeomorph.ulift.symm.totallyDisconnectedSpace
    · exact Homeomorph.ulift.symm.totallyDisconnectedSpace
  exact Analysis.Schwartz.TensorDecomposition.Constructions.finite_product_decomposition (RepresentationTheory.Theta.Kernel.Schwartz.BinaryBlock ι κ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicAnalysis.CM
