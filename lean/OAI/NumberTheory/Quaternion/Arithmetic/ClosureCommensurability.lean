import OAI.NumberTheory.Quaternion.Arithmetic.Commensurability
import OAI.NumberTheory.Quaternion.Arithmetic.CompactQuotientProjection

/-! # Closure Commensurability -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ClosureCommensurability

noncomputable section

/-! Finite relative index survives passage to topological closures. Thus
commensurable arithmetic subgroups give local closures with a common open
subgroup, the topological input for the Lie-algebra argument. -/

open scoped Classical
open Set _root_.Topology

theorem finiteIndex_closure_of_denseRange
    {A L : Type*} [Group A] [Group L]
    [TopologicalSpace L] [IsTopologicalGroup L]
    (f : A →* L) (hd : DenseRange f) (H : Subgroup A) [H.FiniteIndex] :
    (H.map f).topologicalClosure.FiniteIndex := by
  let J := (H.map f).topologicalClosure
  let : IsClosed (J : Set L) := (H.map f).isClosed_topologicalClosure
  let p : A ⧸ H → L ⧸ J := CompactQuotientProjection.quotientProjection f H J (H.map f).le_topologicalClosure
  have hp : (range p).Finite := Set.finite_range p
  have hdq : DenseRange ((QuotientGroup.mk : L → L ⧸ J) ∘ f) :=
    QuotientGroup.mk_surjective.denseRange.comp hd QuotientGroup.continuous_mk
  have hd' : Dense (range p) := hdq.mono (by
    rintro x ⟨a, rfl⟩
    exact ⟨QuotientGroup.mk a, rfl⟩)
  have hsurj : Function.Surjective p := by
    rw [← range_eq_univ]
    exact hp.isClosed.closure_eq ▸ hd'.closure_eq
  let : Finite (L ⧸ J) := Finite.of_surjective p hsurj
  exact Subgroup.finiteIndex_of_finite_quotient

theorem finiteRelIndex_topologicalClosure
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    (H K : Subgroup L) (hindex : H.relIndex K ≠ 0) :
    H.topologicalClosure.relIndex K.topologicalClosure ≠ 0 := by
  let f : K →* K.topologicalClosure := Subgroup.inclusion K.le_topologicalClosure
  have hd : DenseRange f :=
    (denseRange_inclusion_iff K.le_topologicalClosure).mpr Subset.rfl
  let J := H.subgroupOf K
  let : J.FiniteIndex := ⟨hindex⟩
  let : (J.map f).topologicalClosure.FiniteIndex := finiteIndex_closure_of_denseRange f hd J
  have hc : IsClosed (H.topologicalClosure.subgroupOf K.topologicalClosure :
      Set K.topologicalClosure) := H.isClosed_topologicalClosure.preimage continuous_subtype_val
  have hle : (J.map f).topologicalClosure ≤
      H.topologicalClosure.subgroupOf K.topologicalClosure := by
    apply (J.map f).topologicalClosure_minimal _ hc
    rintro _ ⟨x, hx, rfl⟩
    exact H.le_topologicalClosure hx
  exact (Subgroup.finiteIndex_of_le hle).index_ne_zero

theorem commensurable_topologicalClosure
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    {H K : Subgroup L} (h : H.Commensurable K) :
    H.topologicalClosure.Commensurable K.topologicalClosure :=
  ⟨⟨finiteRelIndex_topologicalClosure H K h.1.relIndex_ne_zero⟩,
    ⟨finiteRelIndex_topologicalClosure K H h.2.relIndex_ne_zero⟩⟩

/-- Each of two commensurable closed subgroups contains their intersection
as an open subgroup. -/
theorem commensurable_closures_open_intersection
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    {H K : Subgroup L} (h : H.Commensurable K) :
    IsOpen (H.topologicalClosure.subgroupOf K.topologicalClosure : Set K.topologicalClosure) ∧
      IsOpen (K.topologicalClosure.subgroupOf H.topologicalClosure : Set H.topologicalClosure) := by
  have hc := commensurable_topologicalClosure h
  let : (H.topologicalClosure.subgroupOf K.topologicalClosure).FiniteIndex := ⟨hc.1.relIndex_ne_zero⟩
  let : (K.topologicalClosure.subgroupOf H.topologicalClosure).FiniteIndex := ⟨hc.2.relIndex_ne_zero⟩
  exact ⟨Subgroup.isOpen_of_isClosed_of_finiteIndex _
      (H.isClosed_topologicalClosure.preimage continuous_subtype_val),
    Subgroup.isOpen_of_isClosed_of_finiteIndex _
      (K.isClosed_topologicalClosure.preimage continuous_subtype_val)⟩

/-- Commensurable closed subgroups agree in some ambient neighborhood of
the identity. This is the form needed to compare infinitesimal data. -/
theorem commensurable_closures_eventually_mem_iff
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    {H K : Subgroup L} (h : H.Commensurable K) :
    ∀ᶠ x in 𝓝 (1 : L), x ∈ H.topologicalClosure ↔ x ∈ K.topologicalClosure := by
  obtain ⟨hHK, hKH⟩ := commensurable_closures_open_intersection h
  obtain ⟨U, hU, heU⟩ := isOpen_induced_iff.mp hHK
  obtain ⟨V, hV, heV⟩ := isOpen_induced_iff.mp hKH
  have hUk (x : K.topologicalClosure) : x.val ∈ U ↔ x.val ∈ H.topologicalClosure := by
    change x ∈ Subtype.val ⁻¹' U ↔ x ∈ H.topologicalClosure.subgroupOf K.topologicalClosure
    rw [heU]
    rfl
  have hVh (x : H.topologicalClosure) : x.val ∈ V ↔ x.val ∈ K.topologicalClosure := by
    change x ∈ Subtype.val ⁻¹' V ↔ x ∈ K.topologicalClosure.subgroupOf H.topologicalClosure
    rw [heV]
    rfl
  have hU1 : (1 : L) ∈ U := (hUk 1).mpr H.topologicalClosure.one_mem
  have hV1 : (1 : L) ∈ V := (hVh 1).mpr K.topologicalClosure.one_mem
  filter_upwards [hU.mem_nhds hU1, hV.mem_nhds hV1] with x hxU hxV
  exact ⟨fun hx => (hVh ⟨x, hx⟩).mp hxV, fun hx => (hUk ⟨x, hx⟩).mp hxU⟩

theorem commensurable_closures_nhdsWithin_eq
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    {H K : Subgroup L} (h : H.Commensurable K) :
    𝓝[(H.topologicalClosure : Set L)] (1 : L) =
      𝓝[(K.topologicalClosure : Set L)] (1 : L) := by
  apply nhdsWithin_eq_iff_eventuallyEqSet.mpr
  exact Filter.eventuallyEqSet_iff.mpr (commensurable_closures_eventually_mem_iff h)

end

end OAI.NumberTheory.Quaternion.Arithmetic.ClosureCommensurability
