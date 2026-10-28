import OAI.NumberTheory.ArithmeticGroups.Lattices.StandardLattice
import OAI.NumberTheory.ArithmeticGroups.Lattices.CommensurableLattice
import OAI.NumberTheory.ArithmeticGroups.Lattices.CompactTransport

/-! # Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Lattice.Construction

noncomputable section

/-! Finite covolume for every arithmetic presentation and commensurable subgroup in Lattices. -/

open scoped Classical

theorem arithmetic_isLattice
    {k Gk GInf : Type} [Field k] [NumberField k] [Group Gk] [Group GInf]
    [TopologicalSpace GInf] [IsTopologicalGroup GInf] [T2Space GInf]
    (G : Algebraic.ConnectedSemisimpleKGroup k) (δ : Gk →* GInf) (Γ₀ Γ : Subgroup Gk)
    (hmodel : IntegralLattice.IsArithmeticPresentation G δ Γ₀) (harithmetic : Γ.Commensurable Γ₀) :
    IntegralLattice.IsLattice (Γ.map δ) := by
  obtain ⟨Λ, r, S, e, hcompact, hΓ₀, hδ⟩ := hmodel
  have hc := Discrete.Construction.commensurable_map_of_injective harithmetic r.toMonoidHom r.injective
  rw [hΓ₀] at hc
  have hstd := hc.trans (LatticeStabilizers.Construction.latticeStabilizer_commensurable_standard G.matrixGroup Λ)
  have hdiag := Discrete.Construction.commensurable_map_of_injective hstd (G.matrixGroup.diagonal Set.univ)
    (Discrete.Construction.full_diagonal_injective G.matrixGroup)
  let H := Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G.matrixGroup
  let P := G.matrixGroup.ArchimedeanProduct Set.univ
  let E := Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G.matrixGroup
  let : LocallyCompactSpace H :=
    (Archimedean.IntegralDiscrete.Construction.fullArchimedeanMatrixGroup_closed G.matrixGroup).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : SecondCountableTopology H :=
    (Archimedean.IntegralDiscrete.Construction.fullArchimedeanMatrixGroup_closed G.matrixGroup).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace P := E.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology P := E.toHomeomorph.isEmbedding.secondCountableTopology
  let : PolishSpace P := LocallyCompactGroupPolish.Construction.locallyCompact_group_polish P
  let Δ := (Γ.map r.toMonoidHom).map (G.matrixGroup.diagonal Set.univ)
  have hΔ : IntegralLattice.IsLattice Δ := CommensurableLattice.Construction.lattice_of_commensurable _ _ hdiag (StandardLattice.Construction.standard_arithmetic_isLattice G)
  have hproj : Δ.map (Discrete.Construction.archimedeanProjection G.matrixGroup S) =
      (Γ.map r.toMonoidHom).map (G.matrixGroup.diagonal S) := by
    rw [Subgroup.map_map, Discrete.Construction.projection_diagonal]
  have hdisc : DiscreteTopology (Δ.map (Discrete.Construction.archimedeanProjection G.matrixGroup S)) :=
    hproj.symm ▸ Discrete.Construction.selected_diagonal_arithmetic_discrete G.matrixGroup Λ
      (Γ.map r.toMonoidHom) hc S hcompact
  have hlat := QuotientMeasure.Construction.lattice_map_of_surjective (Discrete.Construction.archimedeanProjection G.matrixGroup S)
    (CompactTransport.Construction.continuous_archimedeanProjection G.matrixGroup S) (CompactTransport.Construction.archimedeanProjection_surjective G.matrixGroup S)
    Δ hΔ hdisc
  have heq : (Γ.map δ).map e.toMonoidHom = Δ.map (Discrete.Construction.archimedeanProjection G.matrixGroup S) := by
    rw [hproj, Subgroup.map_map, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    exact hδ
  apply LatticeEquivTransport.Construction.lattice_of_continuous_equiv_map e
  rwa [heq]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Lattice.Construction
