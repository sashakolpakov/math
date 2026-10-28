import OAI.NumberTheory.ArithmeticGroups.Lattices.MeasurableCosetSection
import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.FiberMeasure
import Mathlib.GroupTheory.Index

/-! # Index Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.IndexLattice.Construction

noncomputable section

/-! Invariant probability measures pass to finite-index subgroups
by measurable enumeration of the finite coset fibers. -/

open scoped Classical
open _root_.MeasureTheory

theorem lattice_of_finiteIndex_subgroup
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [PolishSpace H] [T2Space H]
    (Γ Δ : Subgroup H) (hΓΔ : Γ ≤ Δ) [(Γ.subgroupOf Δ).FiniteIndex]
    (hΔ : IntegralLattice.IsLattice Δ) : IntegralLattice.IsLattice Γ := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace (H ⧸ Γ) := borel (H ⧸ Γ)
  let : BorelSpace (H ⧸ Γ) := ⟨rfl⟩
  let : MeasurableSpace (H ⧸ Δ) := borel (H ⧸ Δ)
  let : BorelSpace (H ⧸ Δ) := ⟨rfl⟩
  obtain ⟨hdisc, μ, hμprob, hμinv⟩ := hΔ
  let : DiscreteTopology Δ := hdisc
  let : DiscreteTopology Γ := DiscreteTopology.of_continuous_injective
    (f := Subgroup.inclusion hΓΔ) (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hΓΔ)
  let : Countable Δ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  obtain ⟨σ, hσ, hσinv⟩ := MeasurableCosetSection.Construction.exists_measurable_coset_section Δ
  let ι := Δ ⧸ Γ.subgroupOf Δ
  let : Fintype ι := Fintype.ofFinite ι
  let e : H ⧸ Γ ≃ (H ⧸ Δ) × ι := Subgroup.quotientEquivProdOfLE' hΓΔ σ hσinv
  have he : ∀ (h : H) (x : H ⧸ Γ), (e (h • x)).1 = h • (e x).1 := by
    intro h x
    obtain ⟨x, rfl⟩ := Quotient.exists_rep x
    rfl
  have hf (i : ι) : Measurable (fun y => e.symm (y, i)) := by
    obtain ⟨a, rfl⟩ := Quotient.exists_rep i
    change Measurable (fun y => (QuotientGroup.mk (σ y * a.val) : H ⧸ Γ))
    exact QuotientGroup.continuous_mk.measurable.comp (hσ.mul_const a.val)
  obtain ⟨ν, hνprob, hνinv⟩ := FiberMeasure.Construction.invariant_probability_of_finite_enumeration (H := H) μ
    (fun i y => e.symm (y, i)) hf (FiberMeasure.Construction.finite_product_fiber_permutation e he)
  exact ⟨inferInstance, ν, hνprob, hνinv⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.IndexLattice.Construction
