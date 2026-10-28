import OAI.NumberTheory.ArithmeticGroups.Lattices.InverseHaarTranslations
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.Cover

/-! # Quotient Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.QuotientLattice.Construction

noncomputable section

/-! Every discrete cocompact subgroup of a second-countable locally
compact Hausdorff group is a lattice. The proof derives left invariance
of inverse Haar measure from a finite fundamental domain. -/

open scoped Classical ENNReal
open Set _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem lattice_of_discrete_compact_quotient
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    (Γ : Subgroup H) [DiscreteTopology Γ] [CompactSpace (H ⧸ Γ)] : IntegralLattice.IsLattice Γ := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : PolishSpace H := by
    let : UniformSpace H := IsTopologicalGroup.rightUniformSpace H
    let : IsRightUniformGroup H := ⟨rfl⟩
    let : CompleteSpace H := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace H
    let : (uniformity H).IsCountablyGenerated :=
      Filter.comap.isCountablyGenerated _ _
    infer_instance
  let : Countable Γ := (TopologicalSpace.separableSpace_iff_countable (α := Γ)).mp inferInstance
  let μ := haar (G := H)
  obtain ⟨C, hC, hcover⟩ := Cover.Construction.exists_compact_cover_of_compact_quotient Γ
  obtain ⟨F, hFC, hFmeas, hF⟩ := FiniteDomainMeasureRigidity.Construction.exists_fundamentalDomain_subset_of_discrete Γ μ.inv C hC.measurableSet
    (fun x => by
      obtain ⟨c, hc, γ, hγ, rfl⟩ := hcover x
      refine ⟨⟨MulOpposite.op γ⁻¹, Γ.inv_mem hγ⟩, ?_⟩
      simpa using hc)
  have hfin : μ.inv F < ⊤ := (measure_mono hFC).trans_lt hC.measure_lt_top
  let : IsMulLeftInvariant μ.inv := InverseHaarTranslations.Construction.inverseHaar_left_invariant_of_finite_fundamentalDomain
    μ (NeZero.ne μ.inv) Γ F hFmeas hF hfin
  exact QuotientMeasure.Construction.lattice_of_finite_fundamental_domain Γ μ.inv (NeZero.ne μ.inv) F hF hfin

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.QuotientLattice.Construction
