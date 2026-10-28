import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.PlaceMinkowskiGap
import OAI.NumberTheory.ArithmeticGroups.Lattices.CompactTransport
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.Place

/-! # Compact Place Arithmetic -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.CompactPlaceArithmetic.Construction

noncomputable section

/-! The compact-real-place compactness implication for the exact Lattices
arithmetic presentation, including commensurable subgroups and selected
archimedean factors. -/

open scoped Classical

theorem standard_arithmetic_compact_of_compact_real_place
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (v : k →+* ℝ) (hv : Algebraic.IsCompactAtRealPlace G v) :
    CompactSpace (G.matrixGroup.ArchimedeanProduct Set.univ ⧸
      (G.matrixGroup.latticeStabilizer (IntegralLattice.FullLattice.standard k G.dimension)).map
        (G.matrixGroup.diagonal Set.univ)) := by
  obtain ⟨ε, hε, hgap⟩ := PlaceMinkowskiGap.Construction.compact_real_place_uniform_minkowski_gap G v hv
  exact GapCompactness.Construction.standardArithmetic_compact_of_uniform_minkowski_gap G.matrixGroup G.connected G.semisimple ε hε hgap

theorem arithmetic_anisotropic_and_compact_of_compact_real_place
    {k Gk GInf : Type} [Field k] [NumberField k] [Group Gk] [Group GInf]
    [TopologicalSpace GInf]
    (G : Algebraic.ConnectedSemisimpleKGroup k) (δ : Gk →* GInf) (Γ₀ Γ : Subgroup Gk)
    (hmodel : IntegralLattice.IsArithmeticPresentation G δ Γ₀) (harithmetic : Γ.Commensurable Γ₀)
    (hplace : ∃ v : k →+* ℝ, Algebraic.IsCompactAtRealPlace G v) :
    Algebraic.IsAnisotropic G ∧ CompactSpace (GInf ⧸ Γ.map δ) := by
  obtain ⟨v, hv⟩ := hplace
  let : CompactSpace (G.matrixGroup.ArchimedeanProduct Set.univ ⧸
      (G.matrixGroup.latticeStabilizer (IntegralLattice.FullLattice.standard k G.dimension)).map
        (G.matrixGroup.diagonal Set.univ)) :=
    standard_arithmetic_compact_of_compact_real_place G v hv
  exact ⟨Place.Construction.anisotropic_of_compact_real_place G v hv,
    CompactTransport.Construction.arithmetic_compact_of_standard_compact G δ Γ₀ Γ hmodel harithmetic⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.CompactPlaceArithmetic.Construction
