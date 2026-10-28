import OAI.AlgebraicGeometry.Comparison.Betti.ExpandingCauchyPrimitives
import OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyLocalDirections

/-! # Expanding Parametric Primitives -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ExpandingParametricPrimitives.Dolbeault

noncomputable section

/-! Actual smooth parameter families of Cauchy primitives on expanding
discs. Their successive differences are holomorphic on the inner disc. -/

open Set _root_.Metric
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

def expandingParametricCauchyPrimitive (g : P × ℂ → F) (n : ℕ) (q : P × ℂ) : F :=
  ExpandingCauchyPrimitives.Dolbeault.expandingCauchyPrimitive (fun z => g (q.1, z)) n q.2

theorem expandingParametricCauchyPrimitive_smooth {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    ContDiff ℝ ∞ (expandingParametricCauchyPrimitive g n) := by
  have h := VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform_smooth
    (ExpandingCauchyPrimitives.Dolbeault.expandingCauchyBump n).contDiff (ExpandingCauchyPrimitives.Dolbeault.expandingCauchyBump n).hasCompactSupport
    (g := fun p z => g (p, z)) isOpen_univ isOpen_univ (subset_univ _) hg.contDiffOn
  apply contDiffOn_univ.mp
  change ContDiffOn ℝ ∞
    (VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform (ExpandingCauchyPrimitives.Dolbeault.expandingCauchyBump n) (fun p z => g (p, z))) univ
  simpa only [univ_prod_univ] using h

theorem expandingParametricCauchyPrimitive_dbar [CompleteSpace F]
    {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g) (n : ℕ) (p : P) {z : ℂ}
    (hz : z ∈ closedBall 0 ((n : ℝ) + 1)) :
    VectorDbar.Dolbeault.vectorDbar (fun w => expandingParametricCauchyPrimitive g n (p, w)) z = g (p, z) :=
  ExpandingCauchyPrimitives.Dolbeault.expandingCauchyPrimitive_dbar_on_closedBall (hg.comp (contDiff_const.prodMk contDiff_id)) n hz

def expandingParametricCauchyDifference (g : P × ℂ → F) (n : ℕ) : P × ℂ → F :=
  fun q => expandingParametricCauchyPrimitive g (n + 1) q - expandingParametricCauchyPrimitive g n q

theorem expandingParametricCauchyDifference_smooth {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    ContDiff ℝ ∞ (expandingParametricCauchyDifference g n) :=
  (expandingParametricCauchyPrimitive_smooth hg (n + 1)).sub
    (expandingParametricCauchyPrimitive_smooth hg n)

theorem expandingParametricCauchyDifference_holomorphic [CompleteSpace F]
    {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g) (n : ℕ) (p : P) :
    DifferentiableOn ℂ (fun z => expandingParametricCauchyDifference g n (p, z))
      (closedBall 0 ((n : ℝ) + 1)) :=
  ExpandingCauchyPrimitives.Dolbeault.expandingCauchyDifference_holomorphic (hg.comp (contDiff_const.prodMk contDiff_id)) n

theorem expandingParametricCauchyPrimitive_preserves_holomorphic_direction
    [CompleteSpace F] [NormedSpace ℂ P] {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (q : P × ℂ) (v : P)
    (hv : ∀ w : ℂ, fderiv ℝ g (q.1, w) (Complex.I • v, 0) =
      Complex.I • fderiv ℝ g (q.1, w) (v, 0)) :
    fderiv ℝ (expandingParametricCauchyPrimitive g n) q (Complex.I • v, 0) =
      Complex.I • fderiv ℝ (expandingParametricCauchyPrimitive g n) q (v, 0) := by
  exact VectorCauchyLocalDirections.Dolbeault.localizedVectorCauchyTransform_preserves_holomorphic_direction
    (ExpandingCauchyPrimitives.Dolbeault.expandingCauchyBump n).contDiff (ExpandingCauchyPrimitives.Dolbeault.expandingCauchyBump n).hasCompactSupport
    (g := fun p z => g (p, z)) isOpen_univ isOpen_univ (subset_univ _) hg.contDiffOn q
    (mem_univ _) v (fun w _ => hv w)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ExpandingParametricPrimitives.Dolbeault
