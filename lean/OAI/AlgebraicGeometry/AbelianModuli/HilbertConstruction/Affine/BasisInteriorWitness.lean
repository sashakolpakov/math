import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Affine
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Combination

/-! # Basis Interior Witness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BasisInteriorWitness

noncomputable section

/-! A finite affine basis gives an explicit point in the interior of
its convex hull. Positivity of its continuous barycentric coordinates
provides an open neighborhood of the centroid. -/
open Set
open scoped Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem affineBasis_centroid_mem_interior {ι : Type*} [Fintype ι] (b : AffineBasis ι ℝ E) :
    Finset.univ.centroid ℝ b ∈ interior (convexHull ℝ (range b)) := by
  have : Nonempty ι := b.nonempty
  let U : Set E := {x | ∀ i, 0 < b.coord i x}
  have hU : IsOpen U := by
    simpa only [U, Set.ofPred_forall] using isOpen_iInter_of_finite (fun i =>
    isOpen_lt continuous_const
      (AffineMap.continuous_linear_iff.mp (b.coord i).linear.continuous_of_finiteDimensional))
  have hsub : U ⊆ convexHull ℝ (range b) := by
    intro x hx
    rw [b.convexHull_eq_nonneg_coord]
    exact fun i => (hx i).le
  apply interior_maximal hsub hU
  intro i
  rw [b.coord_apply_centroid (Finset.mem_univ i)]
  exact inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr Finset.univ_nonempty))

theorem convexHull_interior_nonempty_of_affineSpan_eq_top {s : Set E}
    (hs : affineSpan ℝ s = ⊤) : (interior (convexHull ℝ s)).Nonempty := by
  obtain ⟨t, hts, b, hb⟩ := AffineBasis.exists_affine_subbasis hs
  have ht : t.Finite := b.setFinite
  let : Fintype t := ht.fintype
  have hrange : range b ⊆ s := by
    rw [hb, Subtype.range_coe_subtype]
    exact hts
  exact ⟨Finset.univ.centroid ℝ b,
    interior_mono (convexHull_mono hrange) (affineBasis_centroid_mem_interior b)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BasisInteriorWitness
