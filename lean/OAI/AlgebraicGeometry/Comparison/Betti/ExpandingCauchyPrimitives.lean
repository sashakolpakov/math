import OAI.AlgebraicGeometry.Comparison.Betti.CauchyHolomorphicLocus
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Expanding Cauchy Primitives -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ExpandingCauchyPrimitives.Dolbeault

noncomputable section

/-! Actual smooth Cauchy primitives on an expanding sequence of
closed discs. Successive differences are holomorphic on each smaller
disc, allowing polynomial corrections without changing the equation. -/

open _root_.Metric
open scoped ContDiff

def expandingCauchyBump (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := (n : ℝ) + 1
  rOut := (n : ℝ) + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

def expandingCauchyPrimitive (g : ℂ → F) (n : ℕ) : ℂ → F :=
  VectorCauchyTransform.Dolbeault.vectorCauchyTransform (fun z => expandingCauchyBump n z • g z)

omit [CompleteSpace F] in
theorem expandingCauchyPrimitive_smooth {g : ℂ → F} (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    ContDiff ℝ ∞ (expandingCauchyPrimitive g n) :=
  VectorCauchyTransform.Dolbeault.vectorCauchyTransform_smooth (expandingCauchyBump n).hasCompactSupport.smul_right
    ((expandingCauchyBump n).contDiff.smul hg)

theorem expandingCauchyPrimitive_dbar {g : ℂ → F} (hg : ContDiff ℝ ∞ g) (n : ℕ) (z : ℂ) :
    VectorDbar.Dolbeault.vectorDbar (expandingCauchyPrimitive g n) z = expandingCauchyBump n z • g z :=
  VectorCauchyRightInverse.Dolbeault.vectorDbar_cauchyTransform ((expandingCauchyBump n).contDiff.smul hg)
    (expandingCauchyBump n).hasCompactSupport.smul_right z

theorem expandingCauchyPrimitive_dbar_on_closedBall {g : ℂ → F} (hg : ContDiff ℝ ∞ g)
    (n : ℕ) {z : ℂ} (hz : z ∈ closedBall 0 ((n : ℝ) + 1)) :
    VectorDbar.Dolbeault.vectorDbar (expandingCauchyPrimitive g n) z = g z := by
  rw [expandingCauchyPrimitive_dbar hg n z, (expandingCauchyBump n).one_of_mem_closedBall hz,
    one_smul]

def expandingCauchyDifference (g : ℂ → F) (n : ℕ) : ℂ → F :=
  fun z => expandingCauchyPrimitive g (n + 1) z - expandingCauchyPrimitive g n z

omit [CompleteSpace F] in
theorem expandingCauchyDifference_smooth {g : ℂ → F} (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    ContDiff ℝ ∞ (expandingCauchyDifference g n) :=
  (expandingCauchyPrimitive_smooth hg (n + 1)).sub (expandingCauchyPrimitive_smooth hg n)

theorem expandingCauchyDifference_holomorphic {g : ℂ → F} (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    DifferentiableOn ℂ (expandingCauchyDifference g n) (closedBall 0 ((n : ℝ) + 1)) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply CauchyHolomorphicLocus.Dolbeault.differentiableAt_complex_of_vectorDbar_zero
    ((expandingCauchyDifference_smooth hg n).differentiable (by simp) z)
  unfold expandingCauchyDifference
  rw [CauchyHolomorphicLocus.Dolbeault.vectorDbar_sub
    ((expandingCauchyPrimitive_smooth hg (n + 1)).differentiable (by simp) z)
    ((expandingCauchyPrimitive_smooth hg n).differentiable (by simp) z)]
  rw [expandingCauchyPrimitive_dbar_on_closedBall hg n hz,
    expandingCauchyPrimitive_dbar_on_closedBall hg (n + 1)
      (closedBall_subset_closedBall (by push_cast; linarith) hz), sub_self]

end

end OAI.AlgebraicGeometry.Comparison.Betti.ExpandingCauchyPrimitives.Dolbeault
