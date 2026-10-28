import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.BracketIntegralLattice
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.AdjointSubgroup
import OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeOpenImage

/-! # Adjoint Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.AdjointLattice.Construction

noncomputable section

/-! The integral adjoint preimage is a lattice without an anisotropy assumption. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

theorem archimedeanLieOrderStabilizer_isLattice
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (b : Module.Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) :
    IntegralLattice.IsLattice (AdjointSubgroup.Construction.archimedeanLieOrderStabilizer G hG b) := by
  let H := Lie.BracketStabilizer.Construction.lieBracketMatrixGroup G hG b
  let f := Archimedean.AdjointOpenImage.Construction.archimedeanLieBracketRepresentation G hG b
  let Γ := (SubmoduleOrbit.Construction.submoduleImageStabilizer (LatticeFrameAction.Construction.matrixFrameIntegralAction b) (Lie.MixedLattice.Construction.lieMixedLatticeInSpan G)).subgroupOf H
  let : SigmaCompactSpace (Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) :=
    (Archimedean.IntegralDiscrete.Construction.fullArchimedeanMatrixGroup_closed G).sigmaCompactSpace
  let : LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin m) ℝ) := Archimedean.AdjointProper.Construction.realGeneralLinear_locallyCompact (Fin m)
  let : SecondCountableTopology (Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin m → ℝ))
  let : SecondCountableTopology (Matrix (Fin m) (Fin m) ℝ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  let : SecondCountableTopology (Matrix.GeneralLinearGroup (Fin m) ℝ) :=
    Units.isClosedEmbedding_embedProduct.isEmbedding.secondCountableTopology
  have hH : IsClosed (H : Set (Matrix.GeneralLinearGroup (Fin m) ℝ)) :=
    TensorStabilizer.Construction.multilinearOperationStabilizer_closed b 2 (Minkowski.LieBracket.Construction.lieMixedBracketForm G hG)
  let : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : SecondCountableTopology H := hH.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let ρ := AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b
  let : Finite ρ.ker := AdjointMatrixTopology.Construction.archimedeanLieMatrixCoordinates_kernel_finite G hG hsemi b
  let j : f.ker → ρ.ker := fun x => ⟨x.val, congrArg (fun z : H => z.val) x.property⟩
  let : Finite f.ker := Finite.of_injective j (by
    intro x y he
    exact Subtype.ext (congrArg (fun z : ρ.ker => z.val) he))
  exact LatticeOpenImage.Construction.lattice_comap_of_open_image_finite_kernel f
    (Archimedean.AdjointOpenImage.Construction.continuous_archimedeanLieBracketRepresentation G hG b)
    (Archimedean.AdjointOpenImage.Construction.archimedean_adjoint_image_open G hG hsemi b) Γ
    (Lie.BracketIntegralLattice.Construction.lieBracket_integral_stabilizer_isLattice G hG hsemi b)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.AdjointLattice.Construction
