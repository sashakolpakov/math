import OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyCutoff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Vector Cauchy Local Primitive -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyLocalPrimitive.Dolbeault

noncomputable section

/-! Local vector-valued antiholomorphic primitives with smooth parameters,
constructed by the actual cutoff Cauchy integral. -/

open Set _root_.Metric
open scoped ContDiff _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

def localizedVectorCauchyTransform (χ : ℂ → ℝ) (g : P → ℂ → F) : P × ℂ → F :=
  ParametricVectorCauchy.Dolbeault.parametricVectorCauchyTransform (VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput χ g)

theorem localizedVectorCauchyTransform_smooth {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {g : P → ℂ → F} {S : Set P} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    (hsub : tsupport χ ⊆ U) (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U)) :
    ContDiffOn ℝ ∞ (localizedVectorCauchyTransform χ g) (S ×ˢ univ) :=
  ParametricVectorCauchy.Dolbeault.parametricVectorCauchyTransform_smooth hS hc.isCompact
    (fun p w _ hw => VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput_support χ g p w hw)
    (VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput_smooth hχ hS hU hsub hg)

variable [CompleteSpace F]

theorem localizedVectorCauchyTransform_primitive {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {g : P → ℂ → F} {S : Set P} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    (hsub : tsupport χ ⊆ U) (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U))
    {p : P} (hp : p ∈ S) {w : ℂ} (hw : χ w = 1) :
    VectorDbar.Dolbeault.vectorDbar (fun z => localizedVectorCauchyTransform χ g (p, z)) w = g p w := by
  have h := ParametricVectorCauchy.Dolbeault.parametricVectorCauchyTransform_slice_primitive hc.isCompact
    (fun p z _ hz => VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput_support χ g p z hz)
    (VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput_smooth hχ hS hU hsub hg) hp w
  simpa only [localizedVectorCauchyTransform, VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput, hw, one_smul] using h

theorem exists_parametric_vectorDbar_local_primitive {g : P → ℂ → F}
    {S : Set P} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U)) {x : ℂ} (hx : x ∈ U) :
    ∃ G : P × ℂ → F, ContDiffOn ℝ ∞ G (S ×ˢ univ) ∧
      ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
        ∀ p ∈ S, ∀ w ∈ ball x r, VectorDbar.Dolbeault.vectorDbar (fun z => G (p, z)) w = g p w := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let χ : ContDiffBump x :=
    { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := half_lt_self hr }
  have hsupp : tsupport χ ⊆ U := by rwa [χ.tsupport_eq]
  refine ⟨localizedVectorCauchyTransform χ g,
    localizedVectorCauchyTransform_smooth χ.contDiff χ.hasCompactSupport hS hU hsupp hg,
    r / 2, half_pos hr, ?_, ?_⟩
  · exact (ball_subset_closedBall.trans (closedBall_subset_closedBall (half_le_self hr.le))).trans hsub
  · intro p hp w hw
    apply localizedVectorCauchyTransform_primitive χ.contDiff χ.hasCompactSupport hS hU hsupp hg hp
    exact χ.one_of_mem_closedBall (ball_subset_closedBall hw)

end

end OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyLocalPrimitive.Dolbeault
