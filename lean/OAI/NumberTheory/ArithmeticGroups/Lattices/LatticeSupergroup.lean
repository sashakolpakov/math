import OAI.NumberTheory.ArithmeticGroups.Lattices.CosetMapInclusion

/-! # Lattice Supergroup -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeSupergroup.Construction

noncomputable section

/-! An invariant probability measure pushes forward to a larger
discrete subgroup quotient. -/

open _root_.MeasureTheory

theorem lattice_of_discrete_supergroup
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (Γ Δ : Subgroup H) (hΓΔ : Γ ≤ Δ) (hΓ : IntegralLattice.IsLattice Γ) [DiscreteTopology Δ] :
    IntegralLattice.IsLattice Δ := by
  let : MeasurableSpace (H ⧸ Γ) := borel (H ⧸ Γ)
  let : BorelSpace (H ⧸ Γ) := ⟨rfl⟩
  let : MeasurableSpace (H ⧸ Δ) := borel (H ⧸ Δ)
  let : BorelSpace (H ⧸ Δ) := ⟨rfl⟩
  let hinc : Γ ≤ Δ.comap (MonoidHom.id H) := hΓΔ
  let p := CosetMapInclusion.Construction.cosetMapOfInclusion (MonoidHom.id H) Γ Δ hinc
  have hp : Measurable p :=
    (CosetMapInclusion.Construction.continuous_cosetMapOfInclusion (MonoidHom.id H) continuous_id Γ Δ hinc).measurable
  have he : ∀ (h : H) (x : H ⧸ Γ), p (h • x) = h • p x := by
    intro h x
    obtain ⟨x, rfl⟩ := Quotient.exists_rep x
    rfl
  obtain ⟨_, μ, hμprob, hμinv⟩ := hΓ
  exact ⟨inferInstance, μ.map p, inferInstance,
    QuotientMeasure.Construction.invariant_measure_map_of_surjective (MonoidHom.id H) Function.surjective_id p hp he μ⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeSupergroup.Construction
