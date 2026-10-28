import OAI.Analysis.PDE.Concentration.Packet.UniformBound
import OAI.Analysis.PDE.Concentration.BoundaryGeometry

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Module Matrix OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.Elementwise

/-- The source's polynomial boundary-gradient estimate for an actual
normalized packet solution. It includes all extended-time derivatives and
is uniform over the entire annulus, not only near the input/output slices. -/
theorem normalized_packet_boundary_gradient {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hcap : ∀ η ∈ K, ‖gaussianVelocity η‖ ≤ 1 / 40) :
    ∃ G : ℝ, 0 < G ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)),
      (∀ j, ‖R (EuclideanSpace.single j 1)‖ ≤ 1) →
      ∀ {ι : Type} [Fintype ι] (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
      (m : ι → Option (Fin (n + 1)) → ℤ) (lam : ℝ),
      0 < h → h ≤ 1 → h ≤ a → 0 ≤ lam → Function.Injective m → (∀ j, 0 < κ j) →
      (∀ j i, inner ℝ (packetSpatialFrequency (κ j) (v j)) (R (EuclideanSpace.single i 1)) =
        (m j i : ℝ) * (2 * Real.pi) / 100) →
      (∀ j, h • packetSpatialFrequency (κ j) (v j) ∈ K) →
      (∀ y, ‖packetBaseWave κ cR cI v 0 y‖ ≤ 1) →
      ∀ S : PhysicalPacketSolution R h a κ cR cI v lam,
      ∀ x, (a < ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ ∧
        ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection (n + 1) x).1‖ < 4) →
        OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) a x = 0 →
        ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots S.u x‖ ≤ G / h ^ (5 * (n + 2) + 1) := by
  obtain ⟨B, hB, hb⟩ := normalized_packet_uniform_barrier hK hcap
  refine ⟨B * (40 * ((n : ℝ) + 2) ^ 2), by positivity, ?_⟩
  intro R hR ι inst h a κ cR cI v m lam hh hh1 hha hlam hinj hκ hm hf hnorm S x ht hr
  have hbar := hb R hR h a κ cR cI v m lam hh hh1 hha hlam hinj hκ hm hf hnorm S
  have hg := physical_boundary_gradient_of_local_barrier (hh.trans_le hha)
    (by positivity : 0 ≤ B / h ^ (5 * (n + 2)))
    (fun y hy hr => (S.smooth.contDiffAt hy hr).differentiableAt (by simp))
    (fun y hy => ⟨hbar y hy, S.nonpositive y hy⟩) S.boundary x ht hr
  calc
    _ ≤ (B / h ^ (5 * (n + 2))) * (40 * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 / a) := hg
    _ ≤ (B / h ^ (5 * (n + 2))) * (40 * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 / h) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) hh hha
    _ = _ := by simp only [Nat.cast_add, Nat.cast_one, pow_succ]; ring

end OAI.Analysis.PDE.Concentration
