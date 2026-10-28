import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Compactness.SigmaCompact

/-! # Countable Compact Relations -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableCompactRelations

noncomputable section

/-! A countable cover by closed relations with compact auxiliary
parameters has one fixed relation valid on a nonempty open patch. -/

open Set

theorem isClosed_exists_mem_compact_relation
    {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    (K : Set Z) (hK : IsCompact K) (R : Set (X × Z)) (hR : IsClosed R) :
    IsClosed {x : X | ∃ z ∈ K, (x, z) ∈ R} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let T : Set (X × K) := (fun q : X × K => (q.1, q.2.val)) ⁻¹' R
  have hT : IsClosed T := hR.preimage
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hproj : IsClosed (Prod.fst '' T) := isClosedMap_fst_of_compactSpace T hT
  have heq : Prod.fst '' T = {x : X | ∃ z ∈ K, (x, z) ∈ R} := by
    ext x
    constructor
    · rintro ⟨⟨y, z⟩, hy, rfl⟩
      exact ⟨z.val, z.property, hy⟩
    · rintro ⟨z, hz, hx⟩
      exact ⟨(x, ⟨z, hz⟩), hx, rfl⟩
  exact heq ▸ hproj

theorem exists_open_fixed_compact_relation
    {X Z I : Type*} [TopologicalSpace X] [BaireSpace X] [Nonempty X]
    [TopologicalSpace Z] [Countable I]
    (K : I → Set Z) (hK : ∀ i, IsCompact (K i))
    (R : I → Set (X × Z)) (hR : ∀ i, IsClosed (R i))
    (hcover : ∀ x : X, ∃ i z, z ∈ K i ∧ (x, z) ∈ R i) :
    ∃ (i : I) (O : Set X), IsOpen O ∧ O.Nonempty ∧
      ∀ x ∈ O, ∃ z ∈ K i, (x, z) ∈ R i := by
  let F := fun i => {x : X | ∃ z ∈ K i, (x, z) ∈ R i}
  have hclosed : ∀ i, IsClosed (F i) := fun i =>
    isClosed_exists_mem_compact_relation (K i) (hK i) (R i) (hR i)
  have hall : ⋃ i, F i = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i, z, hz, hrel⟩ := hcover x
    exact mem_iUnion.mpr ⟨i, z, hz, hrel⟩
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed hclosed hall
  exact ⟨i, interior (F i), isOpen_interior, hi,
    fun _ hx => (show interior (F i) ⊆ F i from interior_subset) hx⟩

theorem exists_open_fixed_relation_of_sigmaCompact
    {X Z I : Type*} [TopologicalSpace X] [BaireSpace X] [Nonempty X]
    [TopologicalSpace Z] [SigmaCompactSpace Z] [Countable I]
    (R : I → Set (X × Z)) (hR : ∀ i, IsClosed (R i))
    (hcover : ∀ x : X, ∃ i z, (x, z) ∈ R i) :
    ∃ (i : I) (O : Set X), IsOpen O ∧ O.Nonempty ∧
      ∀ x ∈ O, ∃ z, (x, z) ∈ R i := by
  obtain ⟨⟨i, n⟩, O, hO, hOn, hrel⟩ := exists_open_fixed_compact_relation
    (fun j : I × ℕ => compactCovering Z j.2)
    (fun j => isCompact_compactCovering Z j.2)
    (fun j : I × ℕ => R j.1) (fun j => hR j.1) (by
      intro x
      obtain ⟨i, z, hz⟩ := hcover x
      obtain ⟨n, hn⟩ := exists_mem_compactCovering z
      exact ⟨(i, n), z, hn, hz⟩)
  refine ⟨i, O, hO, hOn, ?_⟩
  intro x hx
  obtain ⟨z, _, hz⟩ := hrel x hx
  exact ⟨z, hz⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CountableCompactRelations
