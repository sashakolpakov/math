import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.AdjointProper
import OAI.NumberTheory.ArithmeticGroups.Lattices.OpenSubgroupCompactQuotient
import OAI.NumberTheory.ArithmeticGroups.Lattices.OpenHomQuotient
import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.AutomorphismCompactness

/-! # Adjoint Integral Quotient Compactness -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointIntegralQuotientCompactness.Construction

noncomputable section

/-! Under anisotropy the actual archimedean group modulo the inverse
image of the integral Lie-lattice stabilizer is compact. This subgroup
has not yet been identified with the original arithmetic stabilizer. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.Module

theorem discrete_subgroupOf_of_discrete
    {G : Type*} [Group G] [TopologicalSpace G] (Γ H : Subgroup G) [DiscreteTopology Γ] :
    DiscreteTopology (Γ.subgroupOf H) := by
  let f : Γ.subgroupOf H → Γ := fun g => ⟨g.val.val, g.property⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro g h he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : Γ => x.val) he

local instance lieMixedLatticeInSpan_normed_discrete_for_adj_compact
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    @DiscreteTopology (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G)
      (@instTopologicalSpaceSubtype (Lie.MixedLattice.Construction.lieMixedSpan G) _
        (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace) :=
  Lie.MixedLattice.Construction.lieMixedLatticeInSpan_discrete G

attribute [local instance] Lie.MixedLattice.Construction.lieMixedLatticeInSpan_isZLattice

theorem anisotropic_archimedean_lie_order_quotient_compact
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G)
    (b : Basis (Fin (finrank ℝ (Lie.MixedLattice.Construction.lieMixedSpan G.matrixGroup))) ℤ (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup)) :
    let B := b.ofZLatticeBasis ℝ
    let Γ := SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction B) (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup)
    CompactSpace (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G.matrixGroup ⧸
      Γ.comap (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G.matrixGroup G.connected B)) := by
  let E := Lie.MixedLattice.Construction.lieMixedSpan G.matrixGroup
  let B := b.ofZLatticeBasis ℝ
  let Γ := SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction B) (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup)
  let H := Lie.BracketStabilizer.Construction.lieBracketMatrixGroup G.matrixGroup G.connected B
  let ρ := Archimedean.AdjointOpenImage.Construction.archimedeanLieBracketRepresentation G.matrixGroup G.connected B
  let I := ρ.range
  let r : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G.matrixGroup →* I := ρ.rangeRestrict
  let ΓH := Γ.subgroupOf H
  have hρ : Continuous ρ := Archimedean.AdjointOpenImage.Construction.continuous_archimedeanLieBracketRepresentation G.matrixGroup G.connected B
  have hr : Continuous r := hρ.subtype_mk _
  have hsurj : Function.Surjective r := by
    rintro ⟨y, x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  let : SigmaCompactSpace (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G.matrixGroup) :=
    (Archimedean.IntegralDiscrete.Construction.fullArchimedeanMatrixGroup_closed G.matrixGroup).sigmaCompactSpace
  let : SigmaCompactSpace I := isSigmaCompact_iff_sigmaCompactSpace.mp (isSigmaCompact_range hρ)
  let : LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin (finrank ℝ E)) ℝ) :=
    Archimedean.AdjointProper.Construction.realGeneralLinear_locallyCompact _
  have hH : IsClosed (H : Set (Matrix.GeneralLinearGroup (Fin (finrank ℝ E)) ℝ)) :=
    Integral.TensorStabilizer.Construction.multilinearOperationStabilizer_closed B 2 (Minkowski.LieBracket.Construction.lieMixedBracketForm G.matrixGroup G.connected)
  let : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : LocallyCompactSpace I :=
    (Archimedean.AdjointOpenImage.Construction.archimedean_adjoint_image_closed G.matrixGroup G.connected G.semisimple B).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : DiscreteTopology Γ := MahlerFrameOf.Construction.matrix_frame_stabilizer_discrete (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup) b
  let : DiscreteTopology ΓH := discrete_subgroupOf_of_discrete Γ H
  let : CompactSpace (H ⧸ ΓH) := Lie.AutomorphismCompactness.Construction.anisotropic_lie_automorphism_quotient_compact G haniso b
  let : CompactSpace (I ⧸ ΓH.subgroupOf I) := OpenSubgroupCompactQuotient.Construction.open_subgroup_quotient_compact I ΓH
    (Archimedean.AdjointOpenImage.Construction.archimedean_adjoint_image_open G.matrixGroup G.connected G.semisimple B)
  exact OpenHomQuotient.Construction.open_surjective_hom_comap_quotient_compact r hsurj hr
    (r.isOpenMap_of_sigmaCompact hsurj hr) (ΓH.subgroupOf I)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointIntegralQuotientCompactness.Construction
