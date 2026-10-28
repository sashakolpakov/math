import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointFaithfulGap
import OAI.NumberTheory.ArithmeticGroups.Lattices.FaithfulGapCompactImage
import OAI.NumberTheory.ArithmeticGroups.Lattices.DiscreteOvergroupIndex
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.AdjointSubgroup

/-! # Adjoint Index -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.AdjointIndex.Construction

noncomputable section

/-! The original standard arithmetic subgroup has finite index in
the integral adjoint preimage, without an anisotropy hypothesis. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module

local instance integralAdjointIndex_normed_discrete
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    @DiscreteTopology (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G)
      (@instTopologicalSpaceSubtype (Lie.MixedLattice.Construction.lieMixedSpan G) _
        (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace) :=
  Lie.MixedLattice.Construction.lieMixedLatticeInSpan_discrete G

attribute [local instance] Lie.MixedLattice.Construction.lieMixedLatticeInSpan_isZLattice

theorem standard_arithmetic_finiteIndex_in_integral_adjoint
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (b : Basis (Fin (finrank ℝ (Lie.MixedLattice.Construction.lieMixedSpan G))) ℤ (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G)) :
    (((Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n).subgroupOf (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G)).subgroupOf
      (AdjointSubgroup.Construction.archimedeanLieOrderStabilizer G hG (b.ofZLatticeBasis ℝ))).FiniteIndex := by
  let H := Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G
  let Γ := (Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n).subgroupOf H
  let Δ := AdjointSubgroup.Construction.archimedeanLieOrderStabilizer G hG (b.ofZLatticeBasis ℝ)
  let f := AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG (b.ofZLatticeBasis ℝ)
  let Ω := SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.ofZLatticeBasis ℝ))
    (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G)
  have hrep : ∀ g ∈ (Δ : Set H), ∃ γ ∈ Ω, f g * γ ∈ ({1} : Set _) := by
    intro g hg
    exact ⟨(f g)⁻¹, Ω.inv_mem hg, by simp⟩
  obtain ⟨ε, hε, hgap⟩ := AdjointFaithfulGap.Construction.integral_faithful_gap_of_adjoint_representatives
    G hG hsemi b {1} isCompact_singleton (Δ : Set H) hrep
  have hfaithful : ∀ g ∈ (Δ : Set H),
      ∀ x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module, x ≠ 0 →
        ε ≤ ‖Archimedean.Quotient.Construction.archimedeanRealRepresentation k n g.val x‖ := by
    intro g hg x hx hx0
    rw [Minkowski.IntegralAction.Construction.standard_vectorLatticeImage_eq_pi] at hx
    choose a ha using fun i => hx i (Set.mem_univ i)
    have he : (fun i => mixedEmbedding k (a i : k)) = x := funext ha
    have ha0 : a ≠ 0 := by
      intro h
      apply hx0
      rw [← he, h]
      simp
      rfl
    have h := hgap g hg a ha0
    rw [he] at h
    exact h
  obtain ⟨C, hC, himage⟩ := FaithfulGapCompactImage.Construction.faithful_gap_compact_arithmetic_image G hG hsemi (Δ : Set H) ε hε hfaithful
  let : LocallyCompactSpace H :=
    (Archimedean.IntegralDiscrete.Construction.fullArchimedeanMatrixGroup_closed G).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : SecondCountableTopology H :=
    (Archimedean.IntegralDiscrete.Construction.fullArchimedeanMatrixGroup_closed G).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let : DiscreteTopology Δ := AdjointSubgroup.Construction.archimedeanLieOrderStabilizer_discrete G hG hsemi b
  let : SigmaCompactSpace Δ := Δ.isClosed_of_discreteTopology.sigmaCompactSpace
  let : DiscreteTopology (Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n) := Archimedean.IntegralDiscrete.Construction.fullArchimedeanIntegralSL_discrete k n
  let : DiscreteTopology Γ := AdjointIntegralQuotientCompactness.Construction.discrete_subgroupOf_of_discrete _ _
  let : IsClosed (Γ : Set H) := Γ.isClosed_of_discreteTopology
  have hΓΔ : Γ ≤ Δ := by
    have h := AdjointSubgroup.Construction.standard_arithmetic_le_lieOrderStabilizer G hG (b.ofZLatticeBasis ℝ)
    rw [Archimedean.Quotient.Construction.fullArchimedean_standard_arithmetic_subgroup G] at h
    exact h
  exact DiscreteOvergroupIndex.Construction.discrete_overgroup_finiteIndex_of_compact_image Γ Δ hΓΔ C hC himage

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.AdjointIndex.Construction
