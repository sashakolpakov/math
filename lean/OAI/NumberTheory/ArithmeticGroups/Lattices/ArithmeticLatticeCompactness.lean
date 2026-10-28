import OAI.NumberTheory.ArithmeticGroups.Lattices.Lattice
import OAI.NumberTheory.ArithmeticGroups.Lattices.AnisotropicCompactness
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.CompactPlaceArithmetic

/-! # Arithmetic Lattice Compactness -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ArithmeticLatticeCompactness

noncomputable section

/-! Lattices: arithmetic lattices, anisotropic compactness, and the compact-real-place criterion. -/

theorem arithmetic_lattice_and_anisotropic_compactness
    {k Gk GInf : Type}
    [Field k] [NumberField k]
    [Group Gk] [Group GInf]
    [TopologicalSpace GInf] [IsTopologicalGroup GInf]
    [T2Space GInf] [LocallyCompactSpace GInf]
    [SecondCountableTopology GInf]
    (G : Algebraic.ConnectedSemisimpleKGroup k)
    (δ : Gk →* GInf)
    (Γ₀ Γ : Subgroup Gk)
    (hmodel : IntegralLattice.IsArithmeticPresentation G δ Γ₀)
    (harithmetic : Γ.Commensurable Γ₀) :
    IntegralLattice.IsLattice (Γ.map δ) ∧
    (Algebraic.IsAnisotropic G →
      CompactSpace (GInf ⧸ Γ.map δ)) ∧
    ((∃ v : k →+* ℝ, Algebraic.IsCompactAtRealPlace G v) →
      Algebraic.IsAnisotropic G ∧
      CompactSpace (GInf ⧸ Γ.map δ)) := by
  exact ⟨Lattice.Construction.arithmetic_isLattice G δ Γ₀ Γ hmodel harithmetic,
    AnisotropicCompactness.Construction.arithmetic_compact_of_anisotropic G δ Γ₀ Γ hmodel harithmetic,
    Compact.CompactPlaceArithmetic.Construction.arithmetic_anisotropic_and_compact_of_compact_real_place G δ Γ₀ Γ hmodel harithmetic⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ArithmeticLatticeCompactness
