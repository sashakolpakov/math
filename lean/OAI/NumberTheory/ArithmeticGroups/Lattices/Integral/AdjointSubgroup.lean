import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointIntegralQuotientCompactness
import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.KernelDiscrete
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.QuotientLattice

/-! # Adjoint Subgroup -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.AdjointSubgroup.Construction

noncomputable section

/-! The integral adjoint stabilizer is discrete, contains the standard
arithmetic subgroup, and is cocompact under anisotropy. The finite-index
comparison is proved in `IntegralAdjointIndex`. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.Module

def archimedeanLieOrderStabilizer
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) : Subgroup (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) :=
  (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G)).comap
    (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b)

theorem standard_arithmetic_le_lieOrderStabilizer
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) :
    (G.latticeStabilizer (IntegralLattice.FullLattice.standard k n)).map (Archimedean.Quotient.Construction.fullArchimedeanRationalPointMap G) ≤
      archimedeanLieOrderStabilizer G hG b := by
  rintro _ ⟨g, hg, rfl⟩
  exact AdjointMatrixTopology.Construction.standard_arithmetic_adjoint_matrix_mem_stabilizer G hG b g hg

local instance lieMixedLatticeInSpan_normed_discrete_for_integral_adj
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    @DiscreteTopology (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G)
      (@instTopologicalSpaceSubtype (Lie.MixedLattice.Construction.lieMixedSpan G) _
        (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace) :=
  Lie.MixedLattice.Construction.lieMixedLatticeInSpan_discrete G

attribute [local instance] Lie.MixedLattice.Construction.lieMixedLatticeInSpan_isZLattice

theorem archimedeanLieOrderStabilizer_discrete
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (b : Basis (Fin (finrank ℝ (Lie.MixedLattice.Construction.lieMixedSpan G))) ℤ (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G)) :
    DiscreteTopology (archimedeanLieOrderStabilizer G hG (b.ofZLatticeBasis ℝ)) := by
  let B := b.ofZLatticeBasis ℝ
  let Γ := SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction B) (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G)
  let : DiscreteTopology Γ := MahlerFrameOf.Construction.matrix_frame_stabilizer_discrete (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G) b
  let : Finite (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG B).ker :=
    AdjointMatrixTopology.Construction.archimedeanLieMatrixCoordinates_kernel_finite G hG hsemi B
  exact Lattices.Finite.KernelDiscrete.Construction.discrete_comap_of_finite_kernel (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG B)
    (AdjointMatrixTopology.Construction.continuous_archimedeanLieMatrixCoordinates G hG B) Γ

theorem anisotropic_archimedeanLieOrderStabilizer_lattice
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G)
    (b : Basis (Fin (finrank ℝ (Lie.MixedLattice.Construction.lieMixedSpan G.matrixGroup))) ℤ (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup)) :
    IntegralLattice.IsLattice (archimedeanLieOrderStabilizer G.matrixGroup G.connected (b.ofZLatticeBasis ℝ)) ∧
      CompactSpace (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G.matrixGroup ⧸
        archimedeanLieOrderStabilizer G.matrixGroup G.connected (b.ofZLatticeBasis ℝ)) := by
  let Δ := archimedeanLieOrderStabilizer G.matrixGroup G.connected (b.ofZLatticeBasis ℝ)
  let : LocallyCompactSpace (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G.matrixGroup) :=
    (Archimedean.IntegralDiscrete.Construction.fullArchimedeanMatrixGroup_closed G.matrixGroup).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : SecondCountableTopology (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G.matrixGroup) :=
    (Archimedean.IntegralDiscrete.Construction.fullArchimedeanMatrixGroup_closed G.matrixGroup).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let : DiscreteTopology Δ := archimedeanLieOrderStabilizer_discrete
    G.matrixGroup G.connected G.semisimple b
  let : CompactSpace (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G.matrixGroup ⧸ Δ) :=
    AdjointIntegralQuotientCompactness.Construction.anisotropic_archimedean_lie_order_quotient_compact G haniso b
  exact ⟨Compact.QuotientLattice.Construction.lattice_of_discrete_compact_quotient Δ, inferInstance⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.AdjointSubgroup.Construction
