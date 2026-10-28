import OAI.NumberTheory.Quaternion.Arithmetic.AdelicLatticeRationalFrame
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.IntegralAction

/-! # Minkowski Lattice Frames -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.MinkowskiLatticeFrames

noncomputable section

/-! Rational determinant-one frames become real determinant-one frames
of the corresponding Minkowski lattices. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.IntegralAction.Construction

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

omit [NumberField F] in
theorem vectorLatticeImage_map_rational (Λ : Submodule (𝓞 F) (Fin n → F))
    (b : Matrix.SpecialLinearGroup (Fin n) F) :
    ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorLatticeImage (Λ.map ((Matrix.SpecialLinearGroup.toLin' b).toLinearMap.restrictScalars (𝓞 F))) =
      (ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorLatticeImage Λ).map ((ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n (ArithmeticGroups.Lattices.Archimedean.ExteriorAction.Construction.fullArchimedeanSLMap F n b)).toLinearMap.restrictScalars ℤ) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorMixedEmbedding (k := F) n z, ⟨z, hz, rfl⟩, ArithmeticGroups.Lattices.Minkowski.IntegralAction.Construction.archimedeanRealRepresentation_diagonal b z⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨Matrix.SpecialLinearGroup.toLin' b z, ⟨z, hz, rfl⟩,
      (ArithmeticGroups.Lattices.Minkowski.IntegralAction.Construction.archimedeanRealRepresentation_diagonal b z).symm⟩

theorem finiteAdelicGroupLattice_minkowski_frame [Nontrivial (Fin n)] (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G) :
    ∃ e : (Fin n → mixedSpace F) ≃ₗ[ℝ] (Fin n → mixedSpace F),
      e.toLinearMap.det = 1 ∧
      ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorLatticeImage (FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g)) =
        (ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorLatticeImage (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n).module).map (e.toLinearMap.restrictScalars ℤ) := by
  obtain ⟨b, hb⟩ := AdelicLatticeRationalFrame.finiteAdelicGroupLattice_rational_frame G g
  refine ⟨ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n (ArithmeticGroups.Lattices.Archimedean.ExteriorAction.Construction.fullArchimedeanSLMap F n b),
    ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation_det F n _, ?_⟩
  rw [hb, vectorLatticeImage_map_rational]

end

end OAI.NumberTheory.Quaternion.Arithmetic.MinkowskiLatticeFrames
