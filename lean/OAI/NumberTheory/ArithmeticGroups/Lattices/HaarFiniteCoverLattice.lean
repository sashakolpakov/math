import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.QuotientLattice

/-! # Haar Finite Cover Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.HaarFiniteCoverLattice.Construction

noncomputable section

/-! A finite-volume cover for inverse Haar measure makes a discrete
subgroup a lattice, deriving unimodularity from a fundamental domain. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem lattice_of_inverseHaar_finite_cover
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ]
    (μ : Measure H) [IsHaarMeasure μ] [InnerRegular μ]
    (D : Set H) (hD : MeasurableSet D) (hfin : μ.inv D < ⊤)
    (hcover : ∀ x : H, ∃ c ∈ D, ∃ γ ∈ Γ, x = c * γ) : IntegralLattice.IsLattice Γ := by
  let : PolishSpace H := by
    let : UniformSpace H := IsTopologicalGroup.rightUniformSpace H
    let : IsRightUniformGroup H := ⟨rfl⟩
    let : CompleteSpace H := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace H
    let : (uniformity H).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
    infer_instance
  let : Countable Γ := (TopologicalSpace.separableSpace_iff_countable (α := Γ)).mp inferInstance
  obtain ⟨F, hFD, hFmeas, hF⟩ := FiniteDomainMeasureRigidity.Construction.exists_fundamentalDomain_subset_of_discrete Γ μ.inv D hD
    (fun x => by
      obtain ⟨c, hc, γ, hγ, rfl⟩ := hcover x
      refine ⟨⟨MulOpposite.op γ⁻¹, Γ.inv_mem hγ⟩, ?_⟩
      simpa using hc)
  have hFfin : μ.inv F < ⊤ := (measure_mono hFD).trans_lt hfin
  let : IsMulLeftInvariant μ.inv := InverseHaarTranslations.Construction.inverseHaar_left_invariant_of_finite_fundamentalDomain
    μ (NeZero.ne μ.inv) Γ F hFmeas hF hFfin
  exact QuotientMeasure.Construction.lattice_of_finite_fundamental_domain Γ μ.inv (NeZero.ne μ.inv) F hF hFfin

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.HaarFiniteCoverLattice.Construction
