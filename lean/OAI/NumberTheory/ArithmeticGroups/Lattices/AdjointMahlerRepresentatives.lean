import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieGap
import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieVolume
import OAI.NumberTheory.ArithmeticGroups.Lattices.MahlerFrameNormed

/-! # Adjoint Mahler Representatives -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointMahlerRepresentatives.Construction

noncomputable section

/-! For an anisotropic Lattices group, its adjoint Minkowski lattices have
compact matrix representatives modulo integral changes of lattice basis. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module

local instance lieMixedLatticeInSpan_normed_discrete
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    @DiscreteTopology (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G)
      (@instTopologicalSpaceSubtype (Lie.MixedLattice.Construction.lieMixedSpan G) _
        (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace) :=
  Lie.MixedLattice.Construction.lieMixedLatticeInSpan_discrete G

attribute [local instance] Lie.MixedLattice.Construction.lieMixedLatticeInSpan_isZLattice

def archimedeanLieMatrixCoordinates
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) :
    Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G →* Matrix.GeneralLinearGroup (Fin m) ℝ :=
  (LatticeFrameAction.Construction.matrixFrameAction b).symm.toMonoidHom.comp (Archimedean.LieMem.Construction.archimedeanLieRepresentation G hG)

theorem archimedeanLieMatrixCoordinates_action
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) (g : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) :
    LatticeFrameAction.Construction.matrixFrameAction b (archimedeanLieMatrixCoordinates G hG b g) =
      Archimedean.LieMem.Construction.archimedeanLieRepresentation G hG g :=
  (LatticeFrameAction.Construction.matrixFrameAction b).apply_symm_apply _

theorem anisotropic_adjoint_compact_lattice_representatives
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G) :
    ∃ b : Basis (Fin (finrank ℝ (Lie.MixedLattice.Construction.lieMixedSpan G.matrixGroup))) ℤ (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup),
      ∃ K : Set (Matrix.GeneralLinearGroup (Fin (finrank ℝ (Lie.MixedLattice.Construction.lieMixedSpan G.matrixGroup))) ℝ),
        IsCompact K ∧ ∀ g : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G.matrixGroup,
          ∃ γ ∈ SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.ofZLatticeBasis ℝ))
              (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup),
            archimedeanLieMatrixCoordinates G.matrixGroup G.connected (b.ofZLatticeBasis ℝ) g * γ ∈ K := by
  let E := Lie.MixedLattice.Construction.lieMixedSpan G.matrixGroup
  let Λ := Lie.MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup
  let : DiscreteTopology Λ := Lie.MixedLattice.Construction.lieMixedLatticeInSpan_discrete G.matrixGroup
  let : IsZLattice ℝ Λ := Lie.MixedLattice.Construction.lieMixedLatticeInSpan_isZLattice G.matrixGroup
  let : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  let : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  let b : Basis (Fin (finrank ℝ E)) ℤ Λ :=
    (Module.finBasis ℤ Λ).reindex (finCongr (ZLattice.rank ℝ Λ))
  obtain ⟨ε, hε, hgap⟩ := Archimedean.LieGap.Construction.anisotropic_archimedeanLie_uniform_gap G haniso
  obtain ⟨K, hK, hrep⟩ := MahlerFrameNormed.Construction.exists_compact_matrix_lattice_representatives_normed Λ b ε hε
  refine ⟨b, K, hK, fun g => ?_⟩
  apply hrep (archimedeanLieMatrixCoordinates G.matrixGroup G.connected (b.ofZLatticeBasis ℝ) g)
  · rw [← LatticeFrameAction.Construction.matrixFrameAction_det (b.ofZLatticeBasis ℝ), archimedeanLieMatrixCoordinates_action]
    exact (Archimedean.LieVolume.Construction.archimedeanLieRepresentation_norm_determinant G.matrixGroup G.connected G.semisimple g)
  · intro x hx hx0
    rw [archimedeanLieMatrixCoordinates_action]
    exact hgap g x hx hx0

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointMahlerRepresentatives.Construction
