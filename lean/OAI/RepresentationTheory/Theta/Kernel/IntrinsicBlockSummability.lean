import OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockCompletion

/-! # Intrinsic Block Summability -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSummability.Intrinsic

noncomputable section

/-! Absolute convergence of the actual product-input kernel in block
coordinates, with an explicit rational reindexing. -/
open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Kernel.IntrinsicSchwartz.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSiegel.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockCompletion.IntrinsicKernel
variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ K₂ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A₁ : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {A₂ : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₂}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A₁) (B₂ : Adelic.DataTheta.ComparisonData F H K₂ A₂)

theorem product_summand (f₁ f₂ : Adelic.FiniteSchwartz.finiteSchwartz F 3)
    (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A₁)) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A₂))
    (ξ₁ : Adelic.BallGeometryData.FrameIndex A₁ → ℂ) (ξ₂ : Adelic.BallGeometryData.FrameIndex A₂ → ℂ)
    (p : (Fin 3 → F) × (Fin 3 → F)) :
    Adelic.Evaluation.finiteSchwartzFunction F 6 (IntrinsicSchwartz.Intrinsic.productInput F 3 3 f₁ f₂)
      (fun i => algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ((IntrinsicBlockCompletion.IntrinsicKernel.positionSplit F).symm p i)) *
      IntrinsicBlockCompletion.IntrinsicKernel.kernel (IntrinsicBlockSiegel.Intrinsic.blockPeriod Z₁ Z₂).matrix (Sum.elim ξ₁ ξ₂)
        (fun i => (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition
          ((IntrinsicBlockCompletion.IntrinsicKernel.positionSplit F).symm p) i : ℝ)) =
    Adelic.DataTheta.thetaSummand B₁ f₁ Z₁.matrix ξ₁ p.1 * Adelic.DataTheta.thetaSummand B₂ f₂ Z₂.matrix ξ₂ p.2 := by
  have hp₁ (i : Fin 3) : (IntrinsicBlockCompletion.IntrinsicKernel.positionSplit F).symm p (Fin.castAdd 3 i) = p.1 i := by
    exact congrArg (fun q : (Fin 3 → F) × (Fin 3 → F) => q.1 i)
      ((IntrinsicBlockCompletion.IntrinsicKernel.positionSplit F).apply_symm_apply p)
  have hp₂ (i : Fin 3) : (IntrinsicBlockCompletion.IntrinsicKernel.positionSplit F).symm p (Fin.natAdd 3 i) = p.2 i := by
    exact congrArg (fun q : (Fin 3 → F) × (Fin 3 → F) => q.2 i)
      ((IntrinsicBlockCompletion.IntrinsicKernel.positionSplit F).apply_symm_apply p)
  have hR : (fun i => (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition
      ((IntrinsicBlockCompletion.IntrinsicKernel.positionSplit F).symm p) i : ℝ)) =
      Sum.elim (fun i => (B₁.rationalPosition p.1 i : ℝ))
        (fun i => (B₂.rationalPosition p.2 i : ℝ)) := by
    simp only [IntrinsicBlockCompletion.IntrinsicKernel.blockPosition, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.prodCongr_apply]
    funext i
    rcases i with i | i <;> rfl
  rw [IntrinsicSchwartz.Intrinsic.productInput_value F 3 3 f₁ f₂, hR, IntrinsicBlockCompletion.IntrinsicKernel.kernel_blocks]
  simp only [hp₁, hp₂, Adelic.DataTheta.thetaSummand, Adelic.DataTheta.rationalWeight, Adelic.DataTheta.gaussianValue, IntrinsicBlockCompletion.IntrinsicKernel.kernel]
  ring

theorem product_summable (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂)
    (f₁ f₂ : Adelic.FiniteSchwartz.finiteSchwartz F 3)
    (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A₁)) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A₂))
    (ξ : (Adelic.BallGeometryData.FrameIndex A₁ ⊕ Adelic.BallGeometryData.FrameIndex A₂) → ℂ) :
    Summable (fun x : Fin 6 → F =>
      Adelic.Evaluation.finiteSchwartzFunction F 6 (IntrinsicSchwartz.Intrinsic.productInput F 3 3 f₁ f₂)
        (fun i => algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (x i)) *
      IntrinsicBlockCompletion.IntrinsicKernel.kernel (IntrinsicBlockSiegel.Intrinsic.blockPeriod Z₁ Z₂).matrix ξ
        (fun i => (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition x i : ℝ))) := by
  let ξ₁ := fun i => ξ (.inl i)
  let ξ₂ := fun i => ξ (.inr i)
  have hξ : ξ = Sum.elim ξ₁ ξ₂ := by funext i; rcases i with i | i <;> rfl
  rw [hξ]
  apply ((IntrinsicBlockCompletion.IntrinsicKernel.positionSplit F).symm.toEquiv.summable_iff).mp
  exact (summable_mul_of_summable_norm (hΘ₁.2.1 f₁ Z₁ ξ₁).norm
    (hΘ₂.2.1 f₂ Z₂ ξ₂).norm).congr
      (fun p => (product_summand B₁ B₂ f₁ f₂ Z₁ Z₂ ξ₁ ξ₂ p).symm)

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSummability.Intrinsic
