import OAI.NumberTheory.Quaternion.Arithmetic.LocalSubgroup

/-! # Embedded Group Openness -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.EmbeddedGroupOpenness

noncomputable section

/-! The proved local tangent criterion applies to any topological group
with a closed faithful matrix or algebra representation. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F]

theorem embedded_group_isOpen_of_tangentSpan_le (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A]
    [FiniteDimensional (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (e : G →* A) (he : IsClosedEmbedding e) (H : Subgroup G) (hH : IsClosed (H : Set G))
    (hspan : LocalSubgroup.primeLocalTangentSpan v ((⊤ : Subgroup G).toSubmonoid.map e) ≤
      LocalSubgroup.primeLocalTangentSpan v (H.toSubmonoid.map e)) : IsOpen (H : Set G) := by
  have hc : IsClosed (H.toSubmonoid.map e : Set A) := he.isClosedMap _ hH
  have hm := LocalSubgroup.tangentSpan_le_implies_local_containment v (H.toSubmonoid.map e)
    ((⊤ : Subgroup G).toSubmonoid.map e) hc hspan
  have ht := he.continuous.tendsto (1 : G)
  rw [map_one] at ht
  have hnear : ∀ᶠ g in 𝓝 (1 : G),
      e g ∈ (⊤ : Subgroup G).toSubmonoid.map e → e g ∈ H.toSubmonoid.map e := ht hm
  apply H.isOpen_of_mem_nhds (g := 1)
  filter_upwards [hnear] with g hg
  obtain ⟨a, ha, hea⟩ := hg ⟨g, by trivial, rfl⟩
  exact he.injective hea ▸ ha

end

end OAI.NumberTheory.Quaternion.Arithmetic.EmbeddedGroupOpenness
