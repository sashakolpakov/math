import OAI.RepresentationTheory.Theta.Geometric.ArithmeticBall
import OAI.RepresentationTheory.Theta.Geometric.Period.ThetaAt
import OAI.Geometry.ComplexBall.QuotientSubmersion

/-! # Arithmetic Ambient Projection -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! The actual arithmetic quotient covering is holomorphic and has
bijective complex derivative in its constructed two-dimensional atlas. -/

set_option backward.isDefEq.respectTransparency false
open scoped _root_.Manifold ContDiff

open OAI.Geometry.ComplexBall.QuotientSubmersion.Arithmetic

theorem ArithmeticAmbientProjection.ballQuotientProjection_derivative (b : ℂ) (hb : b.re < 0)
    (Γ : Subgroup (Geometry.ComplexBall.ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b))
    [ProperlyDiscontinuousSMul Γ (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball b)] [IsCancelSMul Γ (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball b)] (x : Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball b) :
    letI := Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientAtlas b hb Γ
    MDifferentiableAt 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates) (Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientProjection b Γ) x ∧
      Function.Bijective (mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates)
        (Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientProjection b Γ) x) := by
  let : ChartedSpace LinearTheta.BallCoordinates (Geometry.ComplexBall.QuotientAtlas.Arithmetic.BallQuotient b Γ) := Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientAtlas b hb Γ
  let : IsManifold 𝓘(ℂ, LinearTheta.BallCoordinates) 1 (Geometry.ComplexBall.QuotientAtlas.Arithmetic.BallQuotient b Γ) := Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientAtlas_isManifold b hb Γ
  have hm : Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientChart b hb Γ x ∈ atlas LinearTheta.BallCoordinates (Geometry.ComplexBall.QuotientAtlas.Arithmetic.BallQuotient b Γ) := ⟨x, rfl⟩
  have hd := mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, LinearTheta.BallCoordinates)) hm
  have htar := Geometry.ComplexBall.QuotientSubmersion.Arithmetic.ballQuotientChart_target_self b hb Γ x
  have he : ((Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientChart b hb Γ x).symm : LinearTheta.BallCoordinates → Geometry.ComplexBall.QuotientAtlas.Arithmetic.BallQuotient b Γ) =
      Geometry.ComplexBall.QuotientSubmersion.Arithmetic.ballQuotientAmbientProjection b hb Γ := funext (Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientChart_symm_apply b hb Γ x)
  have hfd : MDifferentiableAt 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates)
      (Geometry.ComplexBall.QuotientSubmersion.Arithmetic.ballQuotientAmbientProjection b hb Γ) x.val := he ▸ hd.mdifferentiableAt_symm htar
  have hfb : Function.Bijective (mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates)
      (Geometry.ComplexBall.QuotientSubmersion.Arithmetic.ballQuotientAmbientProjection b hb Γ) x.val) := he ▸ hd.symm.mfderiv_bijective htar
  have hs : MDifferentiableAt 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates)
      (Subtype.val : Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball b → LinearTheta.BallCoordinates) x :=
    (contMDiff_subtype_val (I := 𝓘(ℂ, LinearTheta.BallCoordinates)) (n := ∞)).mdifferentiable (by simp) x
  have hc : Geometry.ComplexBall.QuotientSubmersion.Arithmetic.ballQuotientAmbientProjection b hb Γ ∘ (Subtype.val : Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball b → LinearTheta.BallCoordinates) =
      Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientProjection b Γ := by
    funext y
    change Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientProjection b Γ ((Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballInclusion b hb).symm y.val) = Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientProjection b Γ y
    rw [Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballInclusion_symm_coe]
  have hder := mfderiv_comp x hfd hs
  rw [hc] at hder
  have hder' : (mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates)
      (Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientProjection b Γ) x : LinearTheta.BallCoordinates →L[ℂ] LinearTheta.BallCoordinates) =
      mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates)
        (Geometry.ComplexBall.QuotientSubmersion.Arithmetic.ballQuotientAmbientProjection b hb Γ) x.val := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun l => l v) hder
    change (mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates) (Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientProjection b Γ) x) v =
      (mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates) (Geometry.ComplexBall.QuotientSubmersion.Arithmetic.ballQuotientAmbientProjection b hb Γ) x.val)
        ((mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates)
          (Subtype.val : Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball b → LinearTheta.BallCoordinates) x) v) at h
    rw [Period.ThetaAt.openSubtype_mfderiv] at h
    exact h
  exact ⟨hc ▸ hfd.comp x hs, hder'.symm ▸ hfb⟩

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)

theorem Data.ActiveHeckeThetaData.arithmeticBallProjection_derivative (x : D.domain) :
    letI := D.arithmeticBallAtlas hg hc hgood hdegree
    MDifferentiableAt 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates) D.arithmeticBallProjection x ∧
      Function.Bijective (mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates) D.arithmeticBallProjection x) := by
  let : IsCancelSMul D.archimedeanArithmeticSubgroup D.domain := D.archimedeanArithmetic_free hg hc hgood hdegree
  let : ProperlyDiscontinuousSMul D.archimedeanArithmeticSubgroup D.domain :=
    D.archimedeanArithmetic_properlyDiscontinuous hg hc hgood hdegree
  exact ArithmeticAmbientProjection.ballQuotientProjection_derivative _ hg.reference_admissible.2.2.2.1 D.archimedeanArithmeticSubgroup x

theorem Data.ActiveHeckeThetaData.arithmeticBallProjection_holomorphic :
    letI := D.arithmeticBallAtlas hg hc hgood hdegree
    MDifferentiable 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates) D.arithmeticBallProjection :=
  fun x => (D.arithmeticBallProjection_derivative hg hc hgood hdegree x).1

end

/-! Native ambient coordinates for the original arithmetic quotient,
with their local derivatives and Hausdorff connected topology. -/

set_option backward.isDefEq.respectTransparency false
open scoped _root_.Manifold

open OAI.Geometry.ComplexBall.QuotientSubmersion.Arithmetic

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry)

def Data.ActiveHeckeThetaData.arithmeticAmbientProjection (w : LinearTheta.BallCoordinates) : D.ArithmeticBallQuotient :=
  D.arithmeticBallProjection ((Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballInclusion _ hg.reference_admissible.2.2.2.1).symm w)

theorem Data.ActiveHeckeThetaData.arithmeticAmbientProjection_coe (w : D.domain) :
    D.arithmeticAmbientProjection hg w.val = D.arithmeticBallProjection w := by
  change D.arithmeticBallProjection ((Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballInclusion _ hg.reference_admissible.2.2.2.1).symm w.val) = _
  rw [Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballInclusion_symm_coe]

variable (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s)

theorem Data.ActiveHeckeThetaData.arithmeticAmbientProjection_derivative (w : D.domain) :
    letI := D.arithmeticBallAtlas hg hc hgood hdegree
    MDifferentiableAt (𝓘(ℂ, LinearTheta.BallCoordinates)) (𝓘(ℂ, LinearTheta.BallCoordinates)) (D.arithmeticAmbientProjection hg) w.val ∧
      Function.Bijective (mfderiv (𝓘(ℂ, LinearTheta.BallCoordinates)) (𝓘(ℂ, LinearTheta.BallCoordinates))
        (D.arithmeticAmbientProjection hg) w.val) := by
  let : IsCancelSMul D.archimedeanArithmeticSubgroup D.domain := D.archimedeanArithmetic_free hg hc hgood hdegree
  let : ProperlyDiscontinuousSMul D.archimedeanArithmeticSubgroup D.domain :=
    D.archimedeanArithmetic_properlyDiscontinuous hg hc hgood hdegree
  let : ChartedSpace LinearTheta.BallCoordinates D.ArithmeticBallQuotient := D.arithmeticBallAtlas hg hc hgood hdegree
  let : IsManifold (𝓘(ℂ, LinearTheta.BallCoordinates)) 1 D.ArithmeticBallQuotient := D.arithmeticBallAtlas_isManifold hg hc hgood hdegree
  let c := Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientChart _ hg.reference_admissible.2.2.2.1 D.archimedeanArithmeticSubgroup w
  have hm : c ∈ atlas LinearTheta.BallCoordinates D.ArithmeticBallQuotient := ⟨w, rfl⟩
  have hd := mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, LinearTheta.BallCoordinates)) hm
  have ht : w.val ∈ c.target := Geometry.ComplexBall.QuotientSubmersion.Arithmetic.ballQuotientChart_target_self _ hg.reference_admissible.2.2.2.1 _ w
  have he : (c.symm : LinearTheta.BallCoordinates → D.ArithmeticBallQuotient) = D.arithmeticAmbientProjection hg :=
    funext (Geometry.ComplexBall.QuotientAtlas.Arithmetic.ballQuotientChart_symm_apply _ hg.reference_admissible.2.2.2.1 _ w)
  exact ⟨he ▸ hd.mdifferentiableAt_symm ht, he ▸ hd.symm.mfderiv_bijective ht⟩

include hg hc hgood hdegree

theorem Data.ActiveHeckeThetaData.arithmeticBallQuotient_t2Space : T2Space D.ArithmeticBallQuotient := by
  let : DiscreteTopology D.archimedeanArithmeticSubgroup := D.archimedeanArithmetic_discrete hg hc hgood hdegree
  let : ProperlyDiscontinuousSMul D.archimedeanArithmeticSubgroup D.domain :=
    D.archimedeanArithmetic_properlyDiscontinuous hg hc hgood hdegree
  let : ProperSMul D.archimedeanArithmeticSubgroup D.domain := properlyDiscontinuousSMul_iff_properSMul.mp inferInstance
  infer_instance

theorem Data.ActiveHeckeThetaData.arithmeticBallQuotient_connected : ConnectedSpace D.ArithmeticBallQuotient := by
  let : ConnectedSpace D.domain := Geometry.ComplexBall.ArithmeticQuotientBoostBall.ball_connected _ hg.reference_admissible.2.2.2.1
  exact D.arithmeticBallProjection_surjective.connectedSpace
    (D.arithmeticBallProjection_covering hg hc hgood hdegree).continuous

end

end OAI.RepresentationTheory.Theta.Geometric
