import OAI.NumberTheory.Quaternion.Arithmetic.IntegralCompact

/-! # Compact Factor Projection -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.CompactFactorProjection

noncomputable section

/-! Compactness of the other factors prevents a locally trivial group
projection from having a nondiscrete image. -/

open scoped Classical
open Set Filter _root_.Topology

theorem compact_factor_projection_discrete_of_locally_trivial
    {C B : Type*} [Group C] [Group B]
    [TopologicalSpace C] [TopologicalSpace B] [IsTopologicalGroup C] [IsTopologicalGroup B]
    [CompactSpace C] [T2Space B]
    (H : Subgroup (C × B)) (hH : IsClosed (H : Set (C × B)))
    (hlocal : ∀ᶠ x in 𝓝 (1 : C × B), x ∈ H → x.2 = 1) :
    IsDiscrete (H.map (MonoidHom.snd C B) : Set B) := by
  let f : H →* B := (MonoidHom.snd C B).comp H.subtype
  have hker : IsOpen (f.ker : Set H) := by
    apply f.ker.isOpen_of_mem_nhds (g := 1)
    have ht := continuous_subtype_val.tendsto (1 : H)
    have hn : ∀ᶠ x in 𝓝 (1 : H), (x.val ∈ H → x.val.2 = 1) := ht hlocal
    filter_upwards [hn] with x hx
    exact hx x.property
  have hfclosed : IsClosedMap f :=
    isClosedMap_snd_of_compactSpace.comp hH.isClosedEmbedding_subtypeVal.isClosedMap
  let U : Set B := (f '' (f.ker : Set H)ᶜ)ᶜ
  have hU : IsOpen U := (hfclosed _ hker.isClosed_compl).isOpen_compl
  have hU1 : (1 : B) ∈ U := by
    rintro ⟨x, hx, hfx⟩
    exact hx hfx
  let R := H.map (MonoidHom.snd C B)
  have hpre : (Subtype.val ⁻¹' U : Set R) = {1} := by
    ext x
    constructor
    · intro hx
      apply mem_singleton_iff.mpr
      apply Subtype.ext
      by_contra hne
      obtain ⟨a, ha, hax⟩ := x.property
      exact hx ⟨⟨a, ha⟩, (by exact fun h => hne (hax ▸ h)), hax⟩
    · rintro rfl
      exact hU1
  have hopen : IsOpen ({1} : Set R) := hpre ▸ hU.preimage continuous_subtype_val
  let : DiscreteTopology R := discreteTopology_iff_isOpen_singleton_one.mpr hopen
  exact isDiscrete_iff_discreteTopology.mpr inferInstance

end

end OAI.NumberTheory.Quaternion.Arithmetic.CompactFactorProjection
