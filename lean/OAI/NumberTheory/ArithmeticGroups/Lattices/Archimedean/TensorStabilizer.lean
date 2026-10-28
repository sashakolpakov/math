import OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraDeterminantPreserver
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.IntegralAction

/-! # Tensor Stabilizer -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.TensorStabilizer.Construction

noncomputable section

/-! The real image of the archimedean group is cut out by a finite family
of scalar-multiplication operators and one determinant tensor. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

theorem archimedeanRealRepresentation_range_iff
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (f : (Fin n → mixedSpace k) ≃ₗ[ℝ] (Fin n → mixedSpace k)) :
    (∃ g : ExteriorAction.Construction.FullArchimedeanSL k n, Quotient.Construction.archimedeanRealRepresentation k n g = f) ↔
    (∀ i x, f (mixedEmbedding.latticeBasis k i • x) =
      mixedEmbedding.latticeBasis k i • f x) ∧
    (∀ v : Fin n → Fin n → mixedSpace k,
      Matrix.det (Matrix.of (fun i => f (v i))) = Matrix.det (Matrix.of v)) := by
  constructor
  · rintro ⟨g, rfl⟩
    have h := (AlgebraDeterminantPreserver.Construction.specialLinear_exists_iff_preserves_scalar_and_determinant
      (Quotient.Construction.archimedeanRealRepresentation k n g)).mp ⟨Quotient.Construction.archimedeanMixedSL k n g, rfl⟩
    exact ⟨fun i => h.1 (mixedEmbedding.latticeBasis k i), h.2⟩
  · rintro ⟨hs, hd⟩
    have hscalar : ∀ (a : mixedSpace k) x, f (a • x) = a • f x :=
      ScalarLinearPreserver.Construction.commutes_scalar_of_basis (mixedEmbedding.latticeBasis k) f.toLinearMap hs
    obtain ⟨A, hA⟩ := AlgebraDeterminantPreserver.Construction.specialLinear_exists_of_scalar_and_determinant_preserved f hscalar hd
    obtain ⟨g, hg⟩ := Quotient.Construction.archimedeanMixedSL_surjective k n A
    refine ⟨g, ?_⟩
    change (Matrix.SpecialLinearGroup.toLin' (Quotient.Construction.archimedeanMixedSL k n g)).restrictScalars ℝ = f
    rw [hg]
    exact hA

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.TensorStabilizer.Construction
