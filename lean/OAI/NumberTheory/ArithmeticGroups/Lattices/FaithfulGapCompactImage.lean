import OAI.NumberTheory.ArithmeticGroups.Lattices.GapCompactness

/-! # Faithful Gap Compact Image -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.FaithfulGapCompactImage.Construction

noncomputable section

/-! A faithful lattice gap on a subset gives a compact container for
its image in the actual arithmetic quotient. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module

theorem faithful_gap_compact_arithmetic_image
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (S : Set (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G)) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ g ∈ S, ∀ x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module,
      x ≠ 0 → ε ≤ ‖Archimedean.Quotient.Construction.archimedeanRealRepresentation k n g.val x‖) :
    ∃ C : Set (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G ⧸
      (Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n).subgroupOf (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G)),
      IsCompact C ∧ ∀ g ∈ S, QuotientGroup.mk g ∈ C := by
  let E := Fin n → mixedSpace k
  let Λ := IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module
  let : DiscreteTopology Λ := IntegralLattice.Construction.vectorLatticeImage_discrete _ (IntegralLattice.FullLattice.standard k n).finite
  let : IsZLattice ℝ Λ := ⟨Minkowski.IntegralAction.Construction.standard_vectorLatticeImage_full k n⟩
  let B : Basis (Fin (finrank ℝ E)) ℤ Λ :=
    (Module.finBasis ℤ Λ).reindex (finCongr (ZLattice.rank ℝ Λ))
  let b := B.ofZLatticeBasis ℝ
  let Γ := (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) Λ).comap Matrix.SpecialLinearGroup.toGL
  let F := Minkowski.RealQuotientEmbedding.Construction.minkowskiRealQuotientEmbedding b ∘
    ClosedOrbitQuotient.Construction.subgroupCosetMap (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) (Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n)
  have hF : Topology.IsClosedEmbedding F :=
    (Minkowski.RealQuotientEmbedding.Construction.minkowskiRealQuotientEmbedding_closed b (B.ofZLatticeBasis_span ℝ)).comp
      (Archimedean.Quotient.Construction.fullArchimedeanMatrixGroup_quotient_closedEmbedding G hG hsemi)
  let K := (QuotientGroup.mk : Algebraic.SL (finrank ℝ E) ℝ → Algebraic.SL (finrank ℝ E) ℝ ⧸ Γ) ''
    {g | ∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖LatticeFrameAction.Construction.matrixFrameAction b g.toGL x‖}
  have hK : IsCompact K := MahlerFrameNormed.Construction.mahler_compactness_normed Λ B ε hε
  refine ⟨F ⁻¹' K, hF.isCompact_preimage hK, fun g hg => ?_⟩
  let M := RealSpecialLinearCoordinates.Construction.realSpecialLinearCoordinates (Archimedean.Quotient.Construction.archimedeanRealRepresentation k n)
    (Archimedean.Quotient.Construction.archimedeanRealRepresentation_det k n) b g.val
  refine ⟨M, ?_, ?_⟩
  · change ∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖LatticeFrameAction.Construction.matrixFrameAction b M.toGL x‖
    rw [RealSpecialLinearCoordinates.Construction.realSpecialLinearCoordinates_frame_action]
    exact hgap g hg
  · change QuotientGroup.mk M = Minkowski.RealQuotientEmbedding.Construction.minkowskiRealQuotientEmbedding b
      (ClosedOrbitQuotient.Construction.subgroupCosetMap (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) (Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n)
        (QuotientGroup.mk g))
    rw [ClosedOrbitQuotient.Construction.subgroupCosetMap_mk, EmbeddingRepresentatives.Construction.minkowskiRealQuotientEmbedding_mk]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.FaithfulGapCompactImage.Construction
