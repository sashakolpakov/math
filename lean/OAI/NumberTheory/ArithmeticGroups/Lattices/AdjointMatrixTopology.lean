import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieContinuity
import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.AdjointKernel

/-! # Adjoint Matrix Topology -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointMatrixTopology.Construction

noncomputable section

/-! Continuous matrix coordinates for the finite-kernel archimedean
adjoint action, with its actual arithmetic lattice stabilizer. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module

theorem matrixFrameAction_symm_val
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (e : E ≃ₗ[ℝ] E) :
    ((LatticeFrameAction.Construction.matrixFrameAction b).symm e).val = LinearMap.toMatrix b b e.toLinearMap := by
  have h := congrArg (fun u : E ≃ₗ[ℝ] E => LinearMap.toMatrix b b u.toLinearMap)
    ((LatticeFrameAction.Construction.matrixFrameAction b).apply_symm_apply e)
  rw [LatticeFrameAction.Construction.matrixFrameAction_toLinearMap, LinearMap.toMatrix_toLin] at h
  exact h

theorem archimedeanLieMatrixCoordinates_val
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) (g : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) :
    (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b g).val =
      LinearMap.toMatrix b b (Archimedean.LieMem.Construction.archimedeanLieRepresentation G hG g).toLinearMap :=
  matrixFrameAction_symm_val b _

theorem continuous_matrixFrameCoordinates
    {H E ι : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι]
    (ρ : H →* (E ≃ₗ[ℝ] E)) (b : Basis ι ℝ E)
    (hρ : Continuous (fun a : H × E => ρ a.1 a.2)) :
    Continuous (fun g : H => (LatticeFrameAction.Construction.matrixFrameAction b).symm (ρ g)) := by
  have hv : Continuous (fun g : H => ((LatticeFrameAction.Construction.matrixFrameAction b).symm (ρ g)).val) := by
    simp_rw [matrixFrameAction_symm_val]
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [LinearMap.toMatrix_apply']
    change Continuous (fun g => b.coord i (ρ g (b j)))
    exact (b.coord i).continuous_of_finiteDimensional.comp
      (hρ.comp (continuous_id.prodMk continuous_const))
  apply Units.continuous_iff.mpr
  refine ⟨hv, ?_⟩
  simpa only [Function.comp_def, map_inv] using hv.comp continuous_inv

theorem continuous_archimedeanLieMatrixCoordinates
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) :
    Continuous (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b) := by
  exact continuous_matrixFrameCoordinates (Archimedean.LieMem.Construction.archimedeanLieRepresentation G hG) b
    (Archimedean.LieContinuity.Construction.continuous_archimedeanLieRepresentation_apply G hG)

theorem archimedeanLieMatrixCoordinates_kernel_finite
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) :
    Finite (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b).ker := by
  let : Finite (Archimedean.LieMem.Construction.archimedeanLieRepresentation G hG).ker :=
    Archimedean.AdjointKernel.Construction.archimedeanLieRepresentation_kernel_finite G hG hsemi
  let f : (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b).ker →
      (Archimedean.LieMem.Construction.archimedeanLieRepresentation G hG).ker := fun g => ⟨g.val, by
    change Archimedean.LieMem.Construction.archimedeanLieRepresentation G hG g.val = 1
    rw [← AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates_action G hG b g.val, g.property, map_one]⟩
  apply Finite.of_injective f
  intro x y h
  exact Subtype.ext (congrArg (fun z : (Archimedean.LieMem.Construction.archimedeanLieRepresentation G hG).ker => z.val) h)

theorem standard_arithmetic_adjoint_matrix_mem_stabilizer
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G))
    (g : G.RationalPoints) (hg : g ∈ G.latticeStabilizer (IntegralLattice.FullLattice.standard k n)) :
    AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b (Archimedean.Quotient.Construction.fullArchimedeanRationalPointMap G g) ∈
      SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G) := by
  apply (StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff _ _ _).mpr
  intro x
  change LatticeFrameAction.Construction.matrixFrameAction b
      (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b (Archimedean.Quotient.Construction.fullArchimedeanRationalPointMap G g)) x ∈
        Lie.MixedLattice.Construction.lieMixedLatticeInSpan G ↔ x ∈ Lie.MixedLattice.Construction.lieMixedLatticeInSpan G
  rw [AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates_action]
  exact Archimedean.Lie.Construction.standard_arithmetic_archimedeanLie_lattice_iff G hG g hg x

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointMatrixTopology.Construction
