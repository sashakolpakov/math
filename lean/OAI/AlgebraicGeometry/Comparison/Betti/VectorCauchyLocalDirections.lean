import OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyLocalPrimitive
import OAI.AlgebraicGeometry.Comparison.Betti.ParametricVectorCauchy

/-! # Vector Cauchy Local Directions -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyLocalDirections.Dolbeault

noncomputable section

/-! The constructed local vector primitive preserves every holomorphic
parameter direction of its input. -/

open Set Filter _root_.Metric
open scoped ContDiff _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem localizedVectorCauchyTransform_preserves_holomorphic_direction {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {g : P → ℂ → F} {S : Set P} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    (hsub : tsupport χ ⊆ U) (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U))
    (q : P × ℂ) (hq : q.1 ∈ S) (v : P)
    (hv : ∀ w ∈ U, fderiv ℝ (Function.uncurry g) (q.1, w) (Complex.I • v, 0) =
      Complex.I • fderiv ℝ (Function.uncurry g) (q.1, w) (v, 0)) :
    fderiv ℝ (VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform χ g) q (Complex.I • v, 0) =
      Complex.I • fderiv ℝ (VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform χ g) q (v, 0) := by
  apply ParametricVectorCauchy.Dolbeault.parametricVectorCauchyTransform_preserves_holomorphic_direction hS hc.isCompact
    (fun p w _ hw => VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput_support χ g p w hw)
    (VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput_smooth hχ hS hU hsub hg) q hq v
  intro w
  by_cases hw : w ∈ U
  · rw [VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput_parameterDerivative hχ hS hU hg hq hw,
      VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput_parameterDerivative hχ hS hU hg hq hw, hv w hw, smul_comm]
  · rw [VectorCauchyCutoff.Dolbeault.cutoffVectorCauchyInput_fderiv_zero (fun h => hw (hsub h))]
    change (0 : F) = Complex.I • (0 : F)
    exact (smul_zero _).symm

theorem exists_parametric_vectorDbar_primitive_preserving_directions {g : P → ℂ → F}
    {S : Set P} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U)) {x : ℂ} (hx : x ∈ U) :
    ∃ G : P × ℂ → F, ContDiffOn ℝ ∞ G (S ×ˢ univ) ∧
      ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
        (∀ p ∈ S, ∀ w ∈ ball x r, VectorDbar.Dolbeault.vectorDbar (fun z => G (p, z)) w = g p w) ∧
        (∀ (q : P × ℂ), q.1 ∈ S → ∀ v : P,
          (∀ w ∈ U, fderiv ℝ (Function.uncurry g) (q.1, w) (Complex.I • v, 0) =
            Complex.I • fderiv ℝ (Function.uncurry g) (q.1, w) (v, 0)) →
          fderiv ℝ G q (Complex.I • v, 0) = Complex.I • fderiv ℝ G q (v, 0)) := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let χ : ContDiffBump x :=
    { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := half_lt_self hr }
  have hsupp : tsupport χ ⊆ U := by rwa [χ.tsupport_eq]
  refine ⟨VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform χ g,
    VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform_smooth χ.contDiff χ.hasCompactSupport hS hU hsupp hg,
    r / 2, half_pos hr, ?_, ?_, ?_⟩
  · exact (ball_subset_closedBall.trans (closedBall_subset_closedBall (half_le_self hr.le))).trans hsub
  · intro p hp w hw
    apply VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform_primitive χ.contDiff χ.hasCompactSupport hS hU hsupp hg hp
    exact χ.one_of_mem_closedBall (ball_subset_closedBall hw)
  · exact localizedVectorCauchyTransform_preserves_holomorphic_direction
      χ.contDiff χ.hasCompactSupport hS hU hsupp hg

end

end OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyLocalDirections.Dolbeault
