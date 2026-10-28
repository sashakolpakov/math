import OAI.AlgebraicGeometry.Comparison.Betti.ExpandingParametricPrimitives

/-! # Expanding Parametric Primitives -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ExpandingParametricPrimitives.Dolbeault

noncomputable section

/-! The original expanding Cauchy primitives over an arbitrary open
parameter set, with their actual slice equation and direction preservation. -/

open Set _root_.Metric
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem expandingParametricCauchyPrimitive_smoothOn {S : Set P} (hS : IsOpen S)
    {g : P × ℂ → F} (hg : ContDiffOn ℝ ∞ g (S ×ˢ univ)) (n : ℕ) :
    ContDiffOn ℝ ∞ (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g n) (S ×ˢ univ) :=
  VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform_smooth
    (ExpandingCauchyPrimitives.Dolbeault.expandingCauchyBump n).contDiff (ExpandingCauchyPrimitives.Dolbeault.expandingCauchyBump n).hasCompactSupport
    (g := fun p z => g (p, z)) hS isOpen_univ (subset_univ _) hg

theorem expandingParametricCauchyDifference_smoothOn {S : Set P} (hS : IsOpen S)
    {g : P × ℂ → F} (hg : ContDiffOn ℝ ∞ g (S ×ˢ univ)) (n : ℕ) :
    ContDiffOn ℝ ∞ (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n) (S ×ˢ univ) :=
  (expandingParametricCauchyPrimitive_smoothOn hS hg (n + 1)).sub
    (expandingParametricCauchyPrimitive_smoothOn hS hg n)

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
theorem contDiff_slice_of_contDiffOn_product {S : Set P}
    {g : P × ℂ → F} (hg : ContDiffOn ℝ ∞ g (S ×ˢ univ)) {p : P} (hp : p ∈ S) :
    ContDiff ℝ ∞ (fun z => g (p, z)) := by
  apply contDiffOn_univ.mp
  exact hg.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨hp, mem_univ _⟩)

theorem expandingParametricCauchyPrimitive_dbar_on [CompleteSpace F] {S : Set P}
    {g : P × ℂ → F} (hg : ContDiffOn ℝ ∞ g (S ×ˢ univ)) (n : ℕ) {p : P} (hp : p ∈ S)
    {z : ℂ} (hz : z ∈ closedBall 0 ((n : ℝ) + 1)) :
    VectorDbar.Dolbeault.vectorDbar (fun w => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g n (p, w)) z = g (p, z) :=
  ExpandingCauchyPrimitives.Dolbeault.expandingCauchyPrimitive_dbar_on_closedBall (contDiff_slice_of_contDiffOn_product hg hp) n hz

theorem expandingParametricCauchyDifference_holomorphic_on [CompleteSpace F] {S : Set P}
    {g : P × ℂ → F} (hg : ContDiffOn ℝ ∞ g (S ×ˢ univ)) (n : ℕ) {p : P} (hp : p ∈ S) :
    DifferentiableOn ℂ (fun z => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n (p, z))
      (closedBall 0 ((n : ℝ) + 1)) :=
  ExpandingCauchyPrimitives.Dolbeault.expandingCauchyDifference_holomorphic (contDiff_slice_of_contDiffOn_product hg hp) n

theorem expandingParametricCauchyPrimitive_preserves_direction_on
    [CompleteSpace F] [NormedSpace ℂ P] {S : Set P} (hS : IsOpen S)
    {g : P × ℂ → F} (hg : ContDiffOn ℝ ∞ g (S ×ˢ univ))
    (n : ℕ) (q : P × ℂ) (hq : q.1 ∈ S) (v : P)
    (hv : ∀ w : ℂ, fderiv ℝ g (q.1, w) (Complex.I • v, 0) =
      Complex.I • fderiv ℝ g (q.1, w) (v, 0)) :
    fderiv ℝ (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g n) q (Complex.I • v, 0) =
      Complex.I • fderiv ℝ (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g n) q (v, 0) :=
  VectorCauchyLocalDirections.Dolbeault.localizedVectorCauchyTransform_preserves_holomorphic_direction
    (ExpandingCauchyPrimitives.Dolbeault.expandingCauchyBump n).contDiff (ExpandingCauchyPrimitives.Dolbeault.expandingCauchyBump n).hasCompactSupport
    (g := fun p z => g (p, z)) hS isOpen_univ (subset_univ _) hg q hq v (fun w _ => hv w)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ExpandingParametricPrimitives.Dolbeault
