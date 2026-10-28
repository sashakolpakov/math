import OAI.Geometry.ComplexBall.QuotientAtlas
import OAI.Geometry.ComplexBall.NormalizeSubmersion

/-! # Quotient Submersion -/

namespace OAI.Geometry.ComplexBall.QuotientSubmersion.Arithmetic

noncomputable section

/-! The quotient projection is locally the inverse of an actual atlas
chart. Composing with affine normalization gives the cone submersion. -/

open scoped Classical _root_.Manifold
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData _root_.Topology

variable (b : ℂ) (hb : b.re < 0) (Γ : Subgroup (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b))
  [ProperlyDiscontinuousSMul Γ (ArithmeticQuotientBoostBall.Ball b)] [IsCancelSMul Γ (ArithmeticQuotientBoostBall.Ball b)]

def ballQuotientAmbientProjection (w : ArithmeticQuotientBoostBall.BallCoordinates) : QuotientAtlas.Arithmetic.BallQuotient b Γ :=
  QuotientAtlas.Arithmetic.ballQuotientProjection b Γ ((QuotientAtlas.Arithmetic.ballInclusion b hb).symm w)

lemma ballQuotientChart_target_self (z : ArithmeticQuotientBoostBall.Ball b) :
    z.val ∈ (QuotientAtlas.Arithmetic.ballQuotientChart b hb Γ z).target := by
  change z.val ∈ (QuotientAtlas.Arithmetic.ballInclusion b hb).target ∧
    (QuotientAtlas.Arithmetic.ballInclusion b hb).symm z.val ∈ (QuotientAtlas.Arithmetic.ballQuotientBranch b Γ z).target
  constructor
  · rw [QuotientAtlas.Arithmetic.ballInclusion_target]
    exact z.property
  · rw [QuotientAtlas.Arithmetic.ballInclusion_symm_coe]
    exact (QuotientAtlas.Arithmetic.ballQuotientProjection_covering b Γ).isCoveringMap.isLocalHomeomorph.self_mem_localInverseAt_target

lemma ballQuotientAmbientProjection_submersion (z : ArithmeticQuotientBoostBall.Ball b) :
    letI : ChartedSpace ArithmeticQuotientBoostBall.BallCoordinates (QuotientAtlas.Arithmetic.BallQuotient b Γ) := QuotientAtlas.Arithmetic.ballQuotientAtlas b hb Γ
    MDifferentiableAt 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates) 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates)
      (ballQuotientAmbientProjection b hb Γ) z.val ∧
    Function.Surjective (mfderiv 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates) 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates)
      (ballQuotientAmbientProjection b hb Γ) z.val) := by
  let : ChartedSpace ArithmeticQuotientBoostBall.BallCoordinates (QuotientAtlas.Arithmetic.BallQuotient b Γ) := QuotientAtlas.Arithmetic.ballQuotientAtlas b hb Γ
  let : IsManifold 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates) 1 (QuotientAtlas.Arithmetic.BallQuotient b Γ) := QuotientAtlas.Arithmetic.ballQuotientAtlas_isManifold b hb Γ
  have hm : QuotientAtlas.Arithmetic.ballQuotientChart b hb Γ z ∈ atlas ArithmeticQuotientBoostBall.BallCoordinates (QuotientAtlas.Arithmetic.BallQuotient b Γ) := ⟨z, rfl⟩
  have hd := mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates)) hm
  have htar := ballQuotientChart_target_self b hb Γ z
  have he : ((QuotientAtlas.Arithmetic.ballQuotientChart b hb Γ z).symm : ArithmeticQuotientBoostBall.BallCoordinates → QuotientAtlas.Arithmetic.BallQuotient b Γ) =
      ballQuotientAmbientProjection b hb Γ := funext (QuotientAtlas.Arithmetic.ballQuotientChart_symm_apply b hb Γ z)
  exact ⟨he ▸ hd.mdifferentiableAt_symm htar, he ▸ hd.symm.mfderiv_surjective htar⟩

def coneAmbientProjection (z : ArithmeticQuotientEquationsData.Vec ℂ) : QuotientAtlas.Arithmetic.BallQuotient b Γ :=
  ballQuotientAmbientProjection b hb Γ (NormalizeSubmersion.ArithmeticQuotient.affineNormalize z)

lemma coneAmbientProjection_submersion (z : ArithmeticQuotientBoostBall.Cone b) :
    letI : ChartedSpace ArithmeticQuotientBoostBall.BallCoordinates (QuotientAtlas.Arithmetic.BallQuotient b Γ) := QuotientAtlas.Arithmetic.ballQuotientAtlas b hb Γ
    MDifferentiableAt 𝓘(ℂ, ArithmeticQuotientEquationsData.Vec ℂ) 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates)
      (coneAmbientProjection b hb Γ) z.val ∧
    Function.Surjective (mfderiv 𝓘(ℂ, ArithmeticQuotientEquationsData.Vec ℂ) 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates)
      (coneAmbientProjection b hb Γ) z.val) := by
  let : ChartedSpace ArithmeticQuotientBoostBall.BallCoordinates (QuotientAtlas.Arithmetic.BallQuotient b Γ) := QuotientAtlas.Arithmetic.ballQuotientAtlas b hb Γ
  let : IsManifold 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates) 1 (QuotientAtlas.Arithmetic.BallQuotient b Γ) := QuotientAtlas.Arithmetic.ballQuotientAtlas_isManifold b hb Γ
  have hq := ballQuotientAmbientProjection_submersion b hb Γ (ArithmeticQuotientBoostBall.normalize b z)
  have hn := (NormalizeSubmersion.ArithmeticQuotient.differentiableAt_affineNormalize z.val (ArithmeticQuotientBoostBall.cone_last_ne_zero b z)).mdifferentiableAt
  refine ⟨hq.1.comp z.val hn, ?_⟩
  have he := mfderiv_comp z.val hq.1 hn
  change mfderiv 𝓘(ℂ, ArithmeticQuotientEquationsData.Vec ℂ) 𝓘(ℂ, ArithmeticQuotientBoostBall.BallCoordinates) (coneAmbientProjection b hb Γ) z.val = _ at he
  rw [he, mfderiv_eq_fderiv]
  exact hq.2.comp (NormalizeSubmersion.ArithmeticQuotient.affineNormalize_fderiv_surjective z.val (ArithmeticQuotientBoostBall.cone_last_ne_zero b z))

end

end OAI.Geometry.ComplexBall.QuotientSubmersion.Arithmetic
