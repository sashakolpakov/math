import OAI.NumberTheory.ArithmeticGroups.Lattices.OpenSubgroupCompactQuotient
import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantMeasureEmbedding
import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointIntegralQuotientCompactness

/-! # Open Subgroup Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OpenSubgroupLattice.Construction

noncomputable section

/-! Intersecting a lattice with an open subgroup preserves the lattice
property, by restricting to its open orbit in the quotient. -/

open scoped Classical
open _root_.MeasureTheory Set

theorem open_subgroup_intersection_lattice
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (H Γ : Subgroup G) (hH : IsOpen (H : Set G)) (hΓ : IntegralLattice.IsLattice Γ) :
    IntegralLattice.IsLattice (Γ.subgroupOf H) := by
  let : MeasurableSpace (G ⧸ Γ) := borel (G ⧸ Γ)
  let : BorelSpace (G ⧸ Γ) := ⟨rfl⟩
  let : MeasurableSpace (H ⧸ Γ.subgroupOf H) := borel (H ⧸ Γ.subgroupOf H)
  let : BorelSpace (H ⧸ Γ.subgroupOf H) := ⟨rfl⟩
  obtain ⟨hdisc, μ, hμprob, hμinv⟩ := hΓ
  let : DiscreteTopology Γ := hdisc
  let : DiscreteTopology (Γ.subgroupOf H) := AdjointIntegralQuotientCompactness.Construction.discrete_subgroupOf_of_discrete _ _
  let : SigmaCompactSpace H := (H.isClosed_of_isOpen hH).sigmaCompactSpace
  let p := ClosedOrbitQuotient.Construction.subgroupCosetMap H Γ
  have hp : Topology.IsClosedEmbedding p := StabilizerSaturation.Construction.subgroup_quotient_embedding_of_closed_image H Γ
    (OpenSubgroupCompactQuotient.Construction.open_subgroup_quotient_image_closed H Γ hH)
  have hrange : range p = (QuotientGroup.mk : G → G ⧸ Γ) '' (H : Set G) := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨x, rfl⟩ := Quotient.exists_rep x
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨QuotientGroup.mk (⟨x, hx⟩ : H), rfl⟩
  have hopen : IsOpen (range p) := by
    rw [hrange]
    exact QuotientGroup.isOpenMap_coe _ hH
  have hnonempty : (range p).Nonempty := ⟨p (QuotientGroup.mk (1 : H)), mem_range_self _⟩
  have hpos : 0 < μ (range p) :=
    measure_isOpen_pos_of_smulInvariant_of_ne_zero G (NeZero.ne μ) hopen hnonempty
  have he : ∀ (h : H) (x : H ⧸ Γ.subgroupOf H), p (h • x) = h.val • p x := by
    intro h x
    obtain ⟨x, rfl⟩ := Quotient.exists_rep x
    rfl
  let : SMulInvariantMeasure H (H ⧸ Γ.subgroupOf H) (μ.comap p) :=
    InvariantMeasureEmbedding.Construction.invariant_measure_comap_embedding H.subtype p hp.measurableEmbedding he μ
  have hmass : (μ.comap p) univ = μ (range p) := by
    rw [Measure.comap_apply p hp.injective hp.measurableEmbedding.measurableSet_image' μ MeasurableSet.univ,
      image_univ]
  obtain ⟨ν, hνprob, hνinv⟩ := QuotientMeasure.Construction.invariant_probability_of_finite (H := H) (μ.comap p)
    (by rw [hmass]; exact hpos.ne') (by rw [hmass]; exact measure_ne_top _ _)
  exact ⟨inferInstance, ν, hνprob, hνinv⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OpenSubgroupLattice.Construction
