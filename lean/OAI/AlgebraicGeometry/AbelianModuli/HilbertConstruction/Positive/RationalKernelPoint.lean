import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.InnerInverse
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.NhdsWithin

/-! # Rational Kernel Point -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.RationalKernelPoint

noncomputable section

/-! A homogeneous rational linear system with a strictly positive real
solution has a strictly positive rational solution. A rational projection
onto its kernel preserves rational points, and continuity preserves the
strict inequalities near the given real point. -/
open scoped Classical _root_.Matrix
universe u

theorem rationalMatrix_positive_kernel_point {ι κ : Type u} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (x : κ → ℝ)
    (hx : A.map (algebraMap ℚ ℝ) *ᵥ x = 0) (hxpos : ∀ i, 0 < x i) :
    ∃ q : κ → ℚ, A *ᵥ q = 0 ∧ ∀ i, 0 < q i := by
  obtain ⟨B, hB⟩ := Linear.InnerInverse.matrix_exists_innerInverse A
  let P : Matrix κ κ ℚ := 1 - B * A
  have hAP : A * P = 0 := Linear.InnerInverse.matrix_innerInverse_kernel_projection A B hB
  let PR := P.map (algebraMap ℚ ℝ)
  have hPR : PR = 1 - B.map (algebraMap ℚ ℝ) * A.map (algebraMap ℚ ℝ) := by
    ext i j
    simp [PR, P, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply, apply_ite]
  have hfix : PR *ᵥ x = x := by
    rw [hPR, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hx,
      Matrix.mulVec_zero, sub_zero]
  let U : Set (κ → ℝ) := {y | ∀ i, 0 < (PR *ᵥ y) i}
  have hcont : Continuous (fun y => PR *ᵥ y) :=
    (Matrix.toLin' PR).continuous_of_finiteDimensional
  have hU : IsOpen U := by
    simpa only [U, Set.ofPred_forall, Function.comp_apply] using
      isOpen_iInter_of_finite (fun i =>
        isOpen_lt continuous_const ((continuous_apply i).comp hcont))
  have hxU : x ∈ U := by
    change ∀ i, 0 < (PR *ᵥ x) i
    rw [hfix]
    exact hxpos
  have hd : DenseRange (fun q : κ → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨q, hq⟩ := hd.exists_mem_open hU ⟨x, hxU⟩
  refine ⟨P *ᵥ q, ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, hAP, Matrix.zero_mulVec]
  · intro i
    have hmap := (algebraMap ℚ ℝ).map_mulVec P q i
    have hpos : (0 : ℝ) < algebraMap ℚ ℝ ((P *ᵥ q) i) := hmap.symm ▸ hq i
    change (0 : ℝ) < ((P *ᵥ q) i : ℝ) at hpos
    exact_mod_cast hpos

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.RationalKernelPoint
