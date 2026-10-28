import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.WordMinor
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.WordMinor
import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.OrderFrame
import OAI.NumberTheory.ArithmeticGroups.Lattices.WordMinorGap

/-! # Adjoint Faithful Gap -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointFaithfulGap.Construction

noncomputable section

/-! Compact adjoint representatives and invariant cyclic word minors
give a faithful lattice gap on any subset of the archimedean group. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module

local instance adjointFaithfulGap_normed_discrete
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    @DiscreteTopology (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G)
      (@instTopologicalSpaceSubtype (Lie.MixedLattice.Construction.lieMixedSpan G) _
        (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace) :=
  Lie.MixedLattice.Construction.lieMixedLatticeInSpan_discrete G

attribute [local instance] Lie.MixedLattice.Construction.lieMixedLatticeInSpan_isZLattice

theorem integral_faithful_gap_of_adjoint_representatives
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (b : Basis (Fin m) ℤ (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G))
    (K : Set (Matrix.GeneralLinearGroup (Fin m) ℝ)) (hK : IsCompact K)
    (S : Set (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G))
    (hrep : ∀ g ∈ S, ∃ γ ∈ SubmoduleOrbit.Construction.submoduleImageStabilizer
      (LatticeFrameAction.Construction.matrixFrameIntegralAction (b.ofZLatticeBasis ℝ)) (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G),
        AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG (b.ofZLatticeBasis ℝ) g * γ ∈ K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ S,
      ∀ x : Fin n → 𝓞 k, x ≠ 0 →
        ε ≤ ‖(Archimedean.LieMem.Construction.archimedeanLieUnit G g).val.mulVec
          (fun i => mixedEmbedding k (x i : k))‖ := by
  let bR : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G) := b.ofZLatticeBasis ℝ
  let F : Matrix.GeneralLinearGroup (Fin m) ℝ →
      (Fin m → Matrix (Fin n) (Fin n) (mixedSpace k)) :=
    fun p i => (LatticeFrameAction.Construction.matrixFrameAction bR p (bR i)).val
  have hF : Continuous F := by
    apply continuous_pi
    intro i
    exact continuous_subtype_val.comp (MahlerFrameOf.Construction.continuous_matrixFrameAction bR (bR i))
  obtain ⟨ε, hε, hgap⟩ := WordMinorGap.Construction.compact_matrix_family_word_minor_gap (d := n)
    (F '' K) (hK.image hF) (mixedEmbedding.integerLattice k : Set (mixedSpace k))
    (isDiscrete_iff_discreteTopology.mpr
      (inferInstance : DiscreteTopology (mixedEmbedding.integerLattice k)))
    (mixedEmbedding.integerLattice k).zero_mem
  refine ⟨ε, hε, fun g hg x hx => ?_⟩
  obtain ⟨γ, hγ, hp⟩ := hrep g hg
  obtain ⟨c, hc⟩ := Lie.OrderFrame.Construction.exists_integral_lie_basis_of_frame_change G b γ hγ
  let A := fun i => (c i).val.val
  have hxk : (fun i => (x i : k)) ≠ 0 := by
    intro h
    apply hx
    funext i
    apply Subtype.ext
    exact congrFun h i
  obtain ⟨q, hq0, hq⟩ := Minkowski.WordMinor.Construction.exists_nonzero_minkowski_word_minor G hG hsemi
    A (Lie.OrderFrame.Construction.lieOrder_basis_spans_matrices G c) (fun i => (x i : k)) hxk g
  let p := AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG bR g * γ
  have hconj (i : Fin m) :
      (Archimedean.LieMem.Construction.archimedeanLieUnit G g).val * (A i).map (mixedEmbedding k) *
          ((Archimedean.LieMem.Construction.archimedeanLieUnit G g)⁻¹).val = F p i := by
    rw [hc i]
    change _ = (LatticeFrameAction.Construction.matrixFrameAction bR
      (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG bR g * γ) (bR i)).val
    rw [map_mul, LinearEquiv.mul_apply, AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates_action]
    exact (Archimedean.LieMem.Construction.archimedeanLieEquiv_apply G hG g _).symm
  have hfamily : (fun i => (Archimedean.LieMem.Construction.archimedeanLieUnit G g).val *
      (A i).map (mixedEmbedding k) * ((Archimedean.LieMem.Construction.archimedeanLieUnit G g)⁻¹).val) = F p :=
    funext hconj
  rw [hfamily] at hq
  apply hgap (F p) ⟨p, hp, rfl⟩ _
  refine ⟨q, ?_, ?_⟩
  · rw [hq]
    exact Integral.WordMinor.Construction.integral_lie_word_minor_mem G c q x
  · rw [hq]
    exact fun hz => hq0 ((mixedEmbedding_injective k) (hz.trans (map_zero _).symm))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointFaithfulGap.Construction
