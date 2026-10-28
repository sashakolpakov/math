import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.IndexedProjectiveFrames
import Mathlib.LinearAlgebra.Basis.SMul

/-! # Indexed Frame Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite

noncomputable section

/-! The finite labeled frame condition is invariant under a linear
coordinate isomorphism, relabeling, and rescaling each point by a unit. -/
open scoped Classical
universe u v w
variable {K V W : Type u} [Field K] [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W] {ι : Type v} {τ : Type w} {r : ℕ}

theorem IndexedProjectiveFrames.HasFiniteIndexedProjectiveFrame.map {e : ι → V}
    (h : IndexedProjectiveFrames.HasFiniteIndexedProjectiveFrame (K := K) (r := r) e) (f : V ≃ₗ[K] W) :
    IndexedProjectiveFrames.HasFiniteIndexedProjectiveFrame (K := K) (r := r) (fun i => f (e i)) := by
  obtain ⟨b, σ, hb, j, hj⟩ := h
  refine ⟨b.map f, σ, fun k => ?_, j, fun k => ?_⟩
  · exact congrArg f (hb k)
  · change b.repr (f.symm (f (e j))) k ≠ 0
    rw [f.symm_apply_apply]
    exact hj k

theorem IndexedProjectiveFrames.HasFiniteIndexedProjectiveFrame.reindex {e : ι → V}
    (h : IndexedProjectiveFrames.HasFiniteIndexedProjectiveFrame (K := K) (r := r) e) (q : τ ≃ ι) :
    IndexedProjectiveFrames.HasFiniteIndexedProjectiveFrame (K := K) (r := r) (fun j => e (q j)) := by
  obtain ⟨b, σ, hb, j, hj⟩ := h
  refine ⟨b, fun k => q.symm (σ k), fun k => ?_, q.symm j, fun k => ?_⟩
  · simpa only [q.apply_symm_apply] using hb k
  · simpa only [q.apply_symm_apply] using hj k

theorem IndexedProjectiveFrames.HasFiniteIndexedProjectiveFrame.units_smul {e : ι → V}
    (h : IndexedProjectiveFrames.HasFiniteIndexedProjectiveFrame (K := K) (r := r) e) (z : ι → Kˣ) :
    IndexedProjectiveFrames.HasFiniteIndexedProjectiveFrame (K := K) (r := r) (fun i => (z i : K) • e i) := by
  obtain ⟨b, σ, hb, j, hj⟩ := h
  refine ⟨b.unitsSMul (fun k => z (σ k)), σ, fun k => ?_, j, fun k => ?_⟩
  · rw [Module.Basis.unitsSMul_apply, Units.smul_def, hb k]
  · rw [Module.Basis.repr_unitsSMul, map_smul]
    change (↑((z (σ k))⁻¹) : K) * ((z j : K) * b.repr (e j) k) ≠ 0
    exact mul_ne_zero (Units.ne_zero _) (mul_ne_zero (Units.ne_zero _) (hj k))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite
