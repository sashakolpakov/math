import OAI.NumberTheory.ArithmeticGroups.Lattices.EmbeddingRepresentatives
import OAI.NumberTheory.ArithmeticGroups.Lattices.MahlerFrameNormed

/-! # Gap Compactness -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.GapCompactness.Construction

noncomputable section

/-! A uniform lower bound on nonzero Minkowski lattice vectors implies
compactness of the actual standard arithmetic quotient. The remaining
anisotropic step must establish this lower bound from cocharacters. -/

open scoped Classical _root_.NumberField
open _root_.Module _root_.NumberField _root_.NumberField.mixedEmbedding

theorem standardArithmetic_compact_of_uniform_minkowski_gap
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ g : G.ArchimedeanProduct Set.univ,
      ∀ x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module, x ≠ 0 →
        ε ≤ ‖Archimedean.Quotient.Construction.archimedeanRealRepresentation k n (Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G g).val x‖) :
    CompactSpace (G.ArchimedeanProduct Set.univ ⧸
      (G.latticeStabilizer (IntegralLattice.FullLattice.standard k n)).map (G.diagonal Set.univ)) := by
  let E := Fin n → mixedSpace k
  let Λ := IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module
  let : DiscreteTopology Λ := IntegralLattice.Construction.vectorLatticeImage_discrete _ (IntegralLattice.FullLattice.standard k n).finite
  let : IsZLattice ℝ Λ := ⟨Minkowski.IntegralAction.Construction.standard_vectorLatticeImage_full k n⟩
  let B : Basis (Fin (finrank ℝ E)) ℤ Λ :=
    (Module.finBasis ℤ Λ).reindex (finCongr (ZLattice.rank ℝ Λ))
  let b := B.ofZLatticeBasis ℝ
  let Γ := (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) Λ).comap Matrix.SpecialLinearGroup.toGL
  let F := Minkowski.RealQuotientEmbedding.Construction.minkowskiRealQuotientEmbedding b ∘ StandardEmbedding.Construction.standardArithmeticQuotientEmbedding G
  have hF : Topology.IsClosedEmbedding F :=
    EmbeddingRepresentatives.Construction.standardArithmetic_real_quotient_closedEmbedding G hconn hsemi b (B.ofZLatticeBasis_span ℝ)
  let K := (QuotientGroup.mk : Algebraic.SL (finrank ℝ E) ℝ → Algebraic.SL (finrank ℝ E) ℝ ⧸ Γ) ''
    {g | ∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖LatticeFrameAction.Construction.matrixFrameAction b g.toGL x‖}
  have hK : IsCompact K := MahlerFrameNormed.Construction.mahler_compactness_normed Λ B ε hε
  have hpre : F ⁻¹' K = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    let M := RealSpecialLinearCoordinates.Construction.realSpecialLinearCoordinates (Archimedean.Quotient.Construction.archimedeanRealRepresentation k n)
      (Archimedean.Quotient.Construction.archimedeanRealRepresentation_det k n) b (Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G g).val
    refine ⟨M, ?_, (EmbeddingRepresentatives.Construction.standardArithmeticRealEmbedding_mk G b g).symm⟩
    change ∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖LatticeFrameAction.Construction.matrixFrameAction b M.toGL x‖
    rw [RealSpecialLinearCoordinates.Construction.realSpecialLinearCoordinates_frame_action]
    exact hgap g
  exact ⟨hpre ▸ hF.isCompact_preimage hK⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.GapCompactness.Construction
