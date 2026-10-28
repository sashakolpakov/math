import OAI.NumberTheory.Quaternion.Arithmetic.TangentCone

/-! # Embedded Commensurability -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.EmbeddedCommensurability

noncomputable section

/-! Commensurable subgroup closures have identical tangent cones in
any faithful topological algebra representation. -/

open Set Filter _root_.Topology

theorem embedded_tangentCone_closures_eq_of_commensurable
    {κ A L : Type*} [Field κ] [Ring A] [Module κ A] [TopologicalSpace A] [ContinuousAdd A]
    [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    (e : L →* A) (he : IsEmbedding e) {H J : Subgroup L} (h : H.Commensurable J) :
    tangentConeAt κ (e '' (H.topologicalClosure : Set L)) 1 =
      tangentConeAt κ (e '' (J.topologicalClosure : Set L)) 1 := by
  have hn := congrArg (Filter.map e) (ClosureCommensurability.commensurable_closures_nhdsWithin_eq h)
  rw [he.map_nhdsWithin_eq, he.map_nhdsWithin_eq, map_one] at hn
  exact tangentConeAt_congr hn

end

end OAI.NumberTheory.Quaternion.Arithmetic.EmbeddedCommensurability
