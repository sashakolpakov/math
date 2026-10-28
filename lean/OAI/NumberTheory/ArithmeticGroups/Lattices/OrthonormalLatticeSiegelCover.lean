import OAI.NumberTheory.ArithmeticGroups.Lattices.StandardSiegelRepresentatives

/-! # Orthonormal Lattice Siegel Cover -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OrthonormalLatticeSiegelCover.Construction

noncomputable section

/-! The standard Siegel cover for the integral span of any prescribed
orthonormal coordinate basis. -/

open _root_.Module

theorem orthonormal_lattice_standard_siegel_cover
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (g : Matrix.GeneralLinearGroup (Fin n) ℝ) :
    ∃ γ ∈ SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b.toBasis)
        (Submodule.span ℤ (Set.range b)), StandardSiegelMatrix.Construction.IsStandardSiegelMatrix (g * γ).val := by
  let : DiscreteTopology (Submodule.span ℤ (Set.range b)) :=
    inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range b.toBasis)))
  let : IsZLattice ℝ (Submodule.span ℤ (Set.range b)) :=
    inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range b.toBasis)))
  have hlin : LinearIndependent ℤ b := b.toBasis.linearIndependent.restrict_scalars' ℤ
  let B : Basis (Fin n) ℤ (Submodule.span ℤ (Set.range b)) := Basis.span hlin
  exact StandardSiegelRepresentatives.Construction.standard_siegel_lattice_representatives _ B b (Basis.coe_span_apply hlin) g

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OrthonormalLatticeSiegelCover.Construction
