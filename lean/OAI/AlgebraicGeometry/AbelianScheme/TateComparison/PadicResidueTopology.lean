import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Instances.ZMod

/-! # Padic Residue Topology -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PadicResidueTopology

noncomputable section

/-! Continuity of finite p-adic residue coordinates, proved from their
actual kernel ideals. This will allow compactness to solve compatible
finite-level coefficient equations in an actual Tate inverse limit. -/

variable (q : ℕ) [Fact q.Prime]

theorem padic_residue_fiber (n : ℕ) (a : ZMod (q ^ n)) :
    {z : ℤ_[q] | PadicInt.toZModPow n z = a} =
      Metric.closedBall (a.val : ℤ_[q]) ((q : ℝ) ^ (-(n : ℤ))) := by
  ext z
  change PadicInt.toZModPow n z = a ↔
    dist z (a.val : ℤ_[q]) ≤ (q : ℝ) ^ (-(n : ℤ))
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
    ZMod.natCast_zmod_val, sub_eq_zero]

theorem continuous_padic_residue (n : ℕ) :
    Continuous (PadicInt.toZModPow (p := q) n) := by
  apply continuous_iff_isClosed.mpr
  intro s _
  have he : (PadicInt.toZModPow (p := q) n) ⁻¹' s =
      ⋃ a ∈ s, {z : ℤ_[q] | PadicInt.toZModPow n z = a} := by
    ext z
    simp
  rw [he]
  apply (Set.toFinite s).isClosed_biUnion
  intro a _
  rw [padic_residue_fiber]
  exact Metric.isClosed_closedBall

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PadicResidueTopology
