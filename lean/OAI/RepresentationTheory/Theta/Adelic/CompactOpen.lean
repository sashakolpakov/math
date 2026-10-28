import Mathlib

/-! # Compact Open -/

namespace OAI.RepresentationTheory.Theta.Adelic.CompactOpen

noncomputable section

/-! Compact open subgroups constructed by stabilizing compact open sets.
This supplies the nonarchimedean-group property of the actual finite
special-unitary groups from their usual locally compact topology. -/

open Filter Set
open scoped _root_.Topology Pointwise

variable {G : Type*} [Group G]

def setwiseStabilizer (W : Set G) : Subgroup G where
  carrier := {g | ∀ x, x ∈ W ↔ g * x ∈ W}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    exact (hh x).trans (by simpa only [mul_assoc] using hg (h * x))
  inv_mem' := by
    intro g hg x
    simpa only [mul_inv_cancel_left] using (hg (g⁻¹ * x)).symm

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem compact_open_set_stabilizer_open (W : Set G)
    (hWc : IsCompact W) (hWo : IsOpen W) :
    IsOpen (setwiseStabilizer W : Set G) := by
  obtain ⟨V, hV, hVW⟩ := compact_open_separated_mul_left hWc hWo (Subset.refl W)
  have hVi : ∀ᶠ g : G in 𝓝 1, g⁻¹ ∈ V := by
    exact (by simpa using (continuous_inv : Continuous (fun g : G => g⁻¹)).tendsto (1 : G) :
      Tendsto (fun g : G => g⁻¹) (𝓝 1) (𝓝 1)).eventually hV
  apply (setwiseStabilizer W).isOpen_of_mem_nhds
  filter_upwards [hV, hVi] with g hg hgi
  intro x
  constructor
  · intro hx
    exact hVW (Set.mul_mem_mul hg hx)
  · intro hx
    simpa only [inv_mul_cancel_left] using hVW (Set.mul_mem_mul hgi hx)

theorem compact_open_subgroup_basis
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (U : Set G) (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := by
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨W, hWcl, h1, hW⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.mp (inter_mem hU hC)
  have hWc : IsCompact W := hCc.of_isClosed_subset hWcl.isClosed (fun x hx => (hW hx).2)
  let K : OpenSubgroup G :=
    ⟨setwiseStabilizer W, compact_open_set_stabilizer_open W hWc hWcl.isOpen⟩
  have hKW : (K : Set G) ⊆ W := by
    intro g hg
    have h := (hg 1).mp h1
    simpa only [mul_one] using h
  refine ⟨K, hWc.of_isClosed_subset K.isClosed hKW, ?_⟩
  exact fun g hg => (hW (hKW hg)).1

theorem nonarchimedean_of_locallyCompact_totallyDisconnected
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    NonarchimedeanGroup G where
  is_nonarchimedean U hU := by
    obtain ⟨K, _, hK⟩ := compact_open_subgroup_basis U hU
    exact ⟨K, hK⟩

end

end OAI.RepresentationTheory.Theta.Adelic.CompactOpen
