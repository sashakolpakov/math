import OAI.NumberTheory.ArithmeticGroups.Lattices.GapCompactness
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.Cover
import OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeStabilizers
import OAI.NumberTheory.ArithmeticGroups.Lattices.Discrete

/-! # Compact Transport -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CompactTransport.Construction

noncomputable section

/-! Compactness of the standard full archimedean quotient transfers to
every arithmetic presentation and commensurable arithmetic subgroup. -/

open scoped Classical

theorem continuous_archimedeanProjection
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (S : Set (NumberField.InfinitePlace k)) :
    Continuous (Discrete.Construction.archimedeanProjection G S) := by
  apply continuous_pi
  intro v
  change Continuous (fun g : G.ArchimedeanProduct Set.univ => g ⟨v.val, Set.mem_univ v.val⟩)
  exact continuous_apply _

theorem archimedeanProjection_surjective
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (S : Set (NumberField.InfinitePlace k)) :
    Function.Surjective (Discrete.Construction.archimedeanProjection G S) := by
  intro g
  refine ⟨fun v => if h : v.val ∈ S then g ⟨v.val, h⟩ else 1, ?_⟩
  funext v
  change (if h : v.val ∈ S then g ⟨v.val, h⟩ else 1) = g v
  simp only [v.property, dite_true]

theorem arithmetic_compact_of_standard_compact
    {k Gk GInf : Type} [Field k] [NumberField k] [Group Gk] [Group GInf]
    [TopologicalSpace GInf]
    (G : Algebraic.ConnectedSemisimpleKGroup k) (δ : Gk →* GInf) (Γ₀ Γ : Subgroup Gk)
    (hmodel : IntegralLattice.IsArithmeticPresentation G δ Γ₀) (harithmetic : Γ.Commensurable Γ₀)
    [CompactSpace (G.matrixGroup.ArchimedeanProduct Set.univ ⧸
      (G.matrixGroup.latticeStabilizer (IntegralLattice.FullLattice.standard k G.dimension)).map
        (G.matrixGroup.diagonal Set.univ))] :
    CompactSpace (GInf ⧸ Γ.map δ) := by
  obtain ⟨Λ, r, S, e, _, hΓ₀, hδ⟩ := hmodel
  have hc := Discrete.Construction.commensurable_map_of_injective harithmetic r.toMonoidHom r.injective
  rw [hΓ₀] at hc
  have hstd := hc.trans (LatticeStabilizers.Construction.latticeStabilizer_commensurable_standard G.matrixGroup Λ)
  have hdiag := Discrete.Construction.commensurable_map_of_injective hstd (G.matrixGroup.diagonal Set.univ)
    (Discrete.Construction.full_diagonal_injective G.matrixGroup)
  let : CompactSpace (G.matrixGroup.ArchimedeanProduct Set.univ ⧸
      (Γ.map r.toMonoidHom).map (G.matrixGroup.diagonal Set.univ)) :=
    (Compact.Cover.Construction.compact_quotient_iff_of_commensurable _ _ hdiag).mpr inferInstance
  have hcompact := QuotientMeasure.Construction.compact_quotient_map_of_surjective
    (Discrete.Construction.archimedeanProjection G.matrixGroup S) (continuous_archimedeanProjection G.matrixGroup S)
    (archimedeanProjection_surjective G.matrixGroup S)
    ((Γ.map r.toMonoidHom).map (G.matrixGroup.diagonal Set.univ))
  have heq : (Γ.map δ).map e.toMonoidHom =
      ((Γ.map r.toMonoidHom).map (G.matrixGroup.diagonal Set.univ)).map
        (Discrete.Construction.archimedeanProjection G.matrixGroup S) := by
    rw [Subgroup.map_map, Subgroup.map_map, Discrete.Construction.projection_diagonal, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    exact hδ
  let : CompactSpace (G.matrixGroup.ArchimedeanProduct S ⧸ (Γ.map δ).map e.toMonoidHom) :=
    heq.symm ▸ hcompact
  exact (CosetHomeomorphism.Construction.cosetHomeomorphOfContinuousMulEquiv e (Γ.map δ)).symm.compactSpace

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CompactTransport.Construction
