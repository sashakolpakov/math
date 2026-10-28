import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.AdjointOpenImage
import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.KernelProperMap

/-! # Adjoint Proper -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.AdjointProper.Construction

noncomputable section

/-! The actual archimedean adjoint representation is proper: inverse
images of compact sets of adjoint matrices are compact. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.Module

theorem realGeneralLinear_locallyCompact
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    LocallyCompactSpace (Matrix.GeneralLinearGroup ι ℝ) := by
  let : LocallyCompactSpace (Matrix ι ι ℝ) :=
    inferInstanceAs (LocallyCompactSpace (ι → ι → ℝ))
  let : LocallyCompactSpace (Matrix ι ι ℝ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem archimedeanLieMatrixCoordinates_proper
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G)) :
    IsProperMap (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b) := by
  let : SigmaCompactSpace (ExteriorAction.Construction.fullArchimedeanMatrixGroup G) :=
    (IntegralDiscrete.Construction.fullArchimedeanMatrixGroup_closed G).sigmaCompactSpace
  let : LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin m) ℝ) :=
    realGeneralLinear_locallyCompact (Fin m)
  let : Finite (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b).ker :=
    AdjointMatrixTopology.Construction.archimedeanLieMatrixCoordinates_kernel_finite G hG hsemi b
  exact Lattices.Finite.KernelProperMap.Construction.continuous_hom_finite_kernel_closed_range_proper
    (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b)
    (AdjointMatrixTopology.Construction.continuous_archimedeanLieMatrixCoordinates G hG b)
    (AdjointOpenImage.Construction.archimedeanLieMatrixCoordinates_range_closed G hG hsemi b)

theorem archimedeanLieMatrixCoordinates_compact_preimage
    {k : Type} [Field k] [NumberField k] {n m : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (b : Basis (Fin m) ℝ (Lie.MixedLattice.Construction.lieMixedSpan G))
    (C : Set (Matrix.GeneralLinearGroup (Fin m) ℝ)) (hC : IsCompact C) :
    IsCompact (AdjointMahlerRepresentatives.Construction.archimedeanLieMatrixCoordinates G hG b ⁻¹' C) :=
  (archimedeanLieMatrixCoordinates_proper G hG hsemi b).isCompact_preimage hC

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.AdjointProper.Construction
