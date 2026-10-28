import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.AdjointLattice
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.AdjointIndex
import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.IndexLattice
import OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeEquivTransport
import OAI.NumberTheory.ArithmeticGroups.Lattices.LocallyCompactGroupPolish
import OAI.NumberTheory.ArithmeticGroups.Lattices.StandardEmbedding

/-! # Standard Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.StandardLattice.Construction

noncomputable section

/-! The standard arithmetic subgroup is a lattice in the full archimedean group. -/

open _root_.Module
open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

local instance standardLattice_normed_discrete
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    @DiscreteTopology (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G)
      (@instTopologicalSpaceSubtype (Lie.MixedLattice.Construction.lieMixedSpan G) _
        (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace) :=
  Lie.MixedLattice.Construction.lieMixedLatticeInSpan_discrete G

attribute [local instance] Lie.MixedLattice.Construction.lieMixedLatticeInSpan_isZLattice

theorem standard_arithmetic_matrix_isLattice
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    IntegralLattice.IsLattice ((Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n).subgroupOf (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G)) := by
  let H := Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G
  let Λ := Lie.MixedLattice.Construction.lieMixedLatticeInSpan G
  let b : Basis (Fin (finrank ℝ (Lie.MixedLattice.Construction.lieMixedSpan G))) ℤ Λ :=
    (Module.finBasis ℤ Λ).reindex (finCongr (ZLattice.rank ℝ Λ))
  let Γ := (Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n).subgroupOf H
  let Δ := Integral.AdjointSubgroup.Construction.archimedeanLieOrderStabilizer G hG (b.ofZLatticeBasis ℝ)
  let : LocallyCompactSpace H :=
    (Archimedean.IntegralDiscrete.Construction.fullArchimedeanMatrixGroup_closed G).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : SecondCountableTopology H :=
    (Archimedean.IntegralDiscrete.Construction.fullArchimedeanMatrixGroup_closed G).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let : PolishSpace H := LocallyCompactGroupPolish.Construction.locallyCompact_group_polish H
  let : (Γ.subgroupOf Δ).FiniteIndex := Integral.AdjointIndex.Construction.standard_arithmetic_finiteIndex_in_integral_adjoint G hG hsemi b
  have hΓΔ : Γ ≤ Δ := by
    have ht := Integral.AdjointSubgroup.Construction.standard_arithmetic_le_lieOrderStabilizer G hG (b.ofZLatticeBasis ℝ)
    rwa [Archimedean.Quotient.Construction.fullArchimedean_standard_arithmetic_subgroup] at ht
  exact Finite.IndexLattice.Construction.lattice_of_finiteIndex_subgroup Γ Δ hΓΔ
    (Integral.AdjointLattice.Construction.archimedeanLieOrderStabilizer_isLattice G hG hsemi (b.ofZLatticeBasis ℝ))

theorem standard_arithmetic_isLattice
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k) :
    IntegralLattice.IsLattice ((G.matrixGroup.latticeStabilizer (IntegralLattice.FullLattice.standard k G.dimension)).map
      (G.matrixGroup.diagonal Set.univ)) := by
  apply LatticeEquivTransport.Construction.lattice_of_continuous_equiv_map (Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G.matrixGroup)
  rw [StandardEmbedding.Construction.standardArithmetic_map_pointsEquiv]
  exact standard_arithmetic_matrix_isLattice G.matrixGroup G.connected G.semisimple

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.StandardLattice.Construction
