import OAI.Geometry.Kakeya.Quadratic.Compression
import Mathlib.Topology.MetricSpace.HausdorffDimension

open Set Module
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OAI.Geometry.Kakeya.Quadratic

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D]

def ruledConstraint (P Q : E →ₗ[ℝ] D) : Set (E × ℝ) :=
  {z | P z.1 = z.2 • Q z.1}

/-- The ruled constraint is parametrized by ker P times the real line.
This proves its dimension bound directly, without a manifold dimension
theorem or a Jordan normal form. -/
theorem dimH_ruledConstraint (P Q : E →ₗ[ℝ] D)
    (hs : Function.Surjective (P.prod Q)) :
    dimH (ruledConstraint P Q) ≤ (finrank ℝ E - finrank ℝ D + 1 : ℕ) := by
  obtain ⟨R, hR⟩ := (P.prod Q).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hs)
  have hP (a : D) : P (R (a, 0)) = a :=
    congrArg (fun f : D × D →ₗ[ℝ] D × D => (f (a, 0)).1) hR
  have hQ (a : D) : Q (R (a, 0)) = 0 :=
    congrArg (fun f : D × D →ₗ[ℝ] D × D => (f (a, 0)).2) hR
  let f : P.ker × ℝ → E × ℝ := fun z =>
    ((z.1 : E) + z.2 • R (Q (z.1 : E), 0), z.2)
  have hf : ContDiff ℝ ∞ f := by
    have hc : ContDiff ℝ ∞ (fun z : P.ker => (z : E)) := P.ker.subtypeL.contDiff
    have hRc : ContDiff ℝ ∞ R := R.toContinuousLinearMap.contDiff
    have hQc : ContDiff ℝ ∞ Q := Q.toContinuousLinearMap.contDiff
    dsimp [f]
    fun_prop
  have hsub : ruledConstraint P Q ⊆ Set.range f := by
    intro z hz
    let v : P.ker := ⟨z.1 - z.2 • R (Q z.1, 0), by
      change P (z.1 - z.2 • R (Q z.1, 0)) = 0
      rw [map_sub, map_smul, hP]
      exact sub_eq_zero.mpr hz⟩
    refine ⟨(v, z.2), ?_⟩
    apply Prod.ext
    · change (z.1 - z.2 • R (Q z.1, 0)) +
        z.2 • R (Q (z.1 - z.2 • R (Q z.1, 0)), 0) = z.1
      rw [map_sub, map_smul, hQ, smul_zero, sub_zero]
      abel
    · rfl
  have hPs : Function.Surjective P := by
    intro a
    obtain ⟨x, hx⟩ := hs (a, 0)
    exact ⟨x, congrArg Prod.fst hx⟩
  have hrank := P.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hPs, finrank_top] at hrank
  have hk : finrank ℝ P.ker = finrank ℝ E - finrank ℝ D := by omega
  calc
    dimH (ruledConstraint P Q) ≤ dimH (Set.range f) := dimH_mono hsub
    _ ≤ finrank ℝ (P.ker × ℝ) := (hf.differentiable (by norm_num)).dimH_range_le
    _ = (finrank ℝ E - finrank ℝ D + 1 : ℕ) := by
      rw [Module.finrank_prod, hk, Module.finrank_self]

end OAI.Geometry.Kakeya.Quadratic
