import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointMahlerRepresentatives

/-! # Lie Continuity -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieContinuity.Construction

noncomputable section

/-! Continuity of the actual archimedean adjoint action. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module

theorem continuous_archimedeanLieUnit_matrix
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    Continuous (fun g : ExteriorAction.Construction.fullArchimedeanMatrixGroup G => (LieMem.Construction.archimedeanLieUnit G g).val) := by
  exact continuous_subtype_val.comp ((Quotient.Construction.continuous_archimedeanMixedSL k n).comp continuous_subtype_val)

theorem continuous_archimedeanLieRepresentation_apply
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    Continuous (fun a : ExteriorAction.Construction.fullArchimedeanMatrixGroup G × Lie.MixedLattice.Construction.lieMixedSpan G =>
      LieMem.Construction.archimedeanLieRepresentation G hG a.1 a.2) := by
  apply Continuous.subtype_mk
  simp_rw [LieMem.Construction.matrixUnitConjugationEquiv_apply]
  change Continuous (fun a : ExteriorAction.Construction.fullArchimedeanMatrixGroup G × Lie.MixedLattice.Construction.lieMixedSpan G =>
    (LieMem.Construction.archimedeanLieUnit G a.1).val * a.2.val * ((LieMem.Construction.archimedeanLieUnit G a.1)⁻¹).val)
  have hi : Continuous (fun a : ExteriorAction.Construction.fullArchimedeanMatrixGroup G × Lie.MixedLattice.Construction.lieMixedSpan G =>
      ((LieMem.Construction.archimedeanLieUnit G a.1)⁻¹).val) := by
    simpa only [Function.comp_def, map_inv] using
      (continuous_archimedeanLieUnit_matrix G).comp
        (show Continuous (fun a : ExteriorAction.Construction.fullArchimedeanMatrixGroup G × Lie.MixedLattice.Construction.lieMixedSpan G => a.1⁻¹)
          from continuous_fst.inv)
  exact (((continuous_archimedeanLieUnit_matrix G).comp continuous_fst).matrix_mul
    (continuous_subtype_val.comp continuous_snd)).matrix_mul hi

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieContinuity.Construction
