import OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicFaithfulGap
import OAI.NumberTheory.ArithmeticGroups.Lattices.CompactTransport
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.QuotientLattice

/-! # Anisotropic Compactness -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicCompactness.Construction

noncomputable section

/-! The anisotropic compactness implication for the exact arithmetic
presentations and commensurable subgroups in Lattices. -/

open scoped Classical

theorem standard_arithmetic_compact_of_anisotropic
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) :
    CompactSpace (G.matrixGroup.ArchimedeanProduct Set.univ ⧸
      (G.matrixGroup.latticeStabilizer (IntegralLattice.FullLattice.standard k G.dimension)).map
        (G.matrixGroup.diagonal Set.univ)) := by
  obtain ⟨ε, hε, hgap⟩ := AnisotropicFaithfulGap.Construction.anisotropic_faithful_minkowski_uniform_gap G haniso
  exact GapCompactness.Construction.standardArithmetic_compact_of_uniform_minkowski_gap
    G.matrixGroup G.connected G.semisimple ε hε hgap

theorem arithmetic_compact_of_anisotropic
    {k Gk GInf : Type} [Field k] [NumberField k] [Group Gk] [Group GInf]
    [TopologicalSpace GInf]
    (G : Algebraic.ConnectedSemisimpleKGroup k) (δ : Gk →* GInf) (Γ₀ Γ : Subgroup Gk)
    (hmodel : IntegralLattice.IsArithmeticPresentation G δ Γ₀) (harithmetic : Γ.Commensurable Γ₀)
    (haniso : Algebraic.IsAnisotropic G) : CompactSpace (GInf ⧸ Γ.map δ) := by
  let : CompactSpace (G.matrixGroup.ArchimedeanProduct Set.univ ⧸
      (G.matrixGroup.latticeStabilizer (IntegralLattice.FullLattice.standard k G.dimension)).map
        (G.matrixGroup.diagonal Set.univ)) := standard_arithmetic_compact_of_anisotropic G haniso
  exact CompactTransport.Construction.arithmetic_compact_of_standard_compact G δ Γ₀ Γ hmodel harithmetic

theorem arithmetic_lattice_and_compact_of_anisotropic
    {k Gk GInf : Type} [Field k] [NumberField k] [Group Gk] [Group GInf]
    [TopologicalSpace GInf] [IsTopologicalGroup GInf] [T2Space GInf]
    [LocallyCompactSpace GInf] [SecondCountableTopology GInf]
    (G : Algebraic.ConnectedSemisimpleKGroup k) (δ : Gk →* GInf) (Γ₀ Γ : Subgroup Gk)
    (hmodel : IntegralLattice.IsArithmeticPresentation G δ Γ₀) (harithmetic : Γ.Commensurable Γ₀)
    (haniso : Algebraic.IsAnisotropic G) :
    IntegralLattice.IsLattice (Γ.map δ) ∧ CompactSpace (GInf ⧸ Γ.map δ) := by
  let : CompactSpace (GInf ⧸ Γ.map δ) :=
    arithmetic_compact_of_anisotropic G δ Γ₀ Γ hmodel harithmetic haniso
  let : DiscreteTopology (Γ.map δ) := Discrete.Construction.arithmetic_subgroup_discrete G δ Γ₀ Γ hmodel harithmetic
  exact ⟨Compact.QuotientLattice.Construction.lattice_of_discrete_compact_quotient (Γ.map δ), inferInstance⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicCompactness.Construction
