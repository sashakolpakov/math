import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FrameProjection

/-! # Scaled Frame Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScaledFrameProjection.Multiplicity

noncomputable section

/-! Holomorphic scalar normalization of a frame-gradient projection. -/

theorem scaled_frameProjection_differentiable
    {ι : Type} [Fintype ι] [DecidableEq ι] (O : Set RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates)
    (j : Fin 2 → ι) (a : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates → ℂ) (Q : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates → Matrix ι ι ℂ)
    (ha : DifferentiableOn ℂ a O) (hQ : DifferentiableOn ℂ Q O)
    (hdet : ∀ z ∈ O, (Q z).det ≠ 0) :
    DifferentiableOn ℂ (fun z => a z • FrameProjection.Multiplicity.frameProjection j (Q z)) O := by
  have hM : DifferentiableOn ℂ (fun z => a z • (Q z)⁻¹) O :=
    DifferentiableOn.smul (𝕜 := ℂ) (𝕜' := ℂ) (E := RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (F := ι → ι → ℂ)
      ha (PeriodMatrixFamilies.Multiplicity.matrix_family_inverse_differentiable hQ hdet)
  let F : (ι → ι → ℂ) →L[ℂ] (((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) :=
    LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ι → ι → ℂ)
      (F' := ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) (FrameProjection.Multiplicity.matrixProjection j)
  have hF : Differentiable ℂ F := ContinuousLinearMap.differentiable
    (𝕜 := ℂ) (E := ι → ι → ℂ) (F := ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) F
  have hcomp : DifferentiableOn ℂ (fun z => F (a z • (Q z)⁻¹)) O :=
    Differentiable.comp_differentiableOn (𝕜 := ℂ) (E := RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (F := ι → ι → ℂ)
      (G := ((ι → ℂ) →L[ℂ] ℂ) →L[ℂ] RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent) hF hM
  apply hcomp.congr
  intro z _
  exact ((FrameProjection.Multiplicity.matrixProjection j).map_smul (a z) (Q z)⁻¹).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScaledFrameProjection.Multiplicity
