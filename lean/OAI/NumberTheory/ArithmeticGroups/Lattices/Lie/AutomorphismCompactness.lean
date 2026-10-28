import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.BracketVolume
import OAI.NumberTheory.ArithmeticGroups.Lattices.MahlerFrameOf
import OAI.NumberTheory.ArithmeticGroups.Lattices.MahlerFrameNormed

/-! # Automorphism Compactness -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.AutomorphismCompactness.Construction

noncomputable section

/-! Under anisotropy the full real Minkowski Lie automorphism group
has compact quotient by its integral lattice stabilizer. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module

local instance lieMixedLatticeInSpan_normed_discrete_for_automorphisms
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    @DiscreteTopology (MixedLattice.Construction.lieMixedLatticeInSpan G)
      (@instTopologicalSpaceSubtype (MixedLattice.Construction.lieMixedSpan G) _
        (inferInstance : NormedAddCommGroup (MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace) :=
  MixedLattice.Construction.lieMixedLatticeInSpan_discrete G

attribute [local instance] MixedLattice.Construction.lieMixedLatticeInSpan_isZLattice

theorem anisotropic_lie_automorphism_quotient_compact
    {k : Type} [Field k] [NumberField k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (haniso : Algebraic.IsAnisotropic G)
    (b : Basis (Fin (finrank ℝ (MixedLattice.Construction.lieMixedSpan G.matrixGroup))) ℤ (MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup)) :
    let B := b.ofZLatticeBasis ℝ
    let H := BracketStabilizer.Construction.lieBracketMatrixGroup G.matrixGroup G.connected B
    let Γ := SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction B) (MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup)
    CompactSpace (H ⧸ Γ.subgroupOf H) := by
  let E := MixedLattice.Construction.lieMixedSpan G.matrixGroup
  let Λ := MixedLattice.Construction.lieMixedLatticeInSpan G.matrixGroup
  let m := finrank ℝ E
  let B := b.ofZLatticeBasis ℝ
  let H := BracketStabilizer.Construction.lieBracketMatrixGroup G.matrixGroup G.connected B
  let Γ := SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction B) Λ
  have hB : Submodule.span ℤ (Set.range B) = Λ := b.ofZLatticeBasis_span ℝ
  let : DiscreteTopology Γ := MahlerFrameOf.Construction.matrix_frame_stabilizer_discrete Λ b
  let : LocallyCompactSpace (Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin m → Fin m → ℝ))
  let : SigmaCompactSpace (Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (SigmaCompactSpace (Fin m → Fin m → ℝ))
  let : SigmaCompactSpace (Matrix (Fin m) (Fin m) ℝ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  let : SigmaCompactSpace (Matrix.GeneralLinearGroup (Fin m) ℝ) :=
    Units.isClosedEmbedding_embedProduct.sigmaCompactSpace
  have hH : IsClosed (H : Set (Matrix.GeneralLinearGroup (Fin m) ℝ)) :=
    Integral.TensorStabilizer.Construction.multilinearOperationStabilizer_closed B 2 (Minkowski.LieBracket.Construction.lieMixedBracketForm G.matrixGroup G.connected)
  let : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : SigmaCompactSpace H := hH.sigmaCompactSpace
  have hclosed : IsClosed ((QuotientGroup.mk : Matrix.GeneralLinearGroup (Fin m) ℝ →
      Matrix.GeneralLinearGroup (Fin m) ℝ ⧸ Γ) '' (H : Set (Matrix.GeneralLinearGroup (Fin m) ℝ))) :=
    BracketStabilizer.Construction.lieBracketMatrixGroup_quotient_image_closed G.matrixGroup G.connected B hB
  obtain ⟨ε, hε, hgap⟩ := Minkowski.LieBracketUniformGap.Construction.anisotropic_bracket_group_uniform_gap G haniso B hB
  obtain ⟨C, hC, hrep⟩ := MahlerFrameNormed.Construction.exists_compact_matrix_lattice_representatives_normed Λ b ε hε
  apply StabilizerSaturation.Construction.compact_subgroup_quotient_of_compact_container H Γ hclosed
    ((QuotientGroup.mk : Matrix.GeneralLinearGroup (Fin m) ℝ → Matrix.GeneralLinearGroup (Fin m) ℝ ⧸ Γ) '' C)
    (hC.image (QuotientGroup.continuous_mk (N := Γ)))
  intro g hg
  obtain ⟨γ, hγ, hγC⟩ := hrep g
    (BracketVolume.Construction.lieBracketMatrixGroup_abs_determinant G.matrixGroup G.connected G.semisimple B g hg)
    (hgap ⟨g, hg⟩)
  exact ⟨g * γ, hγC, QuotientGroup.mk_mul_of_mem g hγ⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.AutomorphismCompactness.Construction
