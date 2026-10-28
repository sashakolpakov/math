import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteFlatKernelTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff

/-! # Prime Block Splitting -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrimeBlockSplitting

noncomputable section

/-! The specified splitting of the native q¹-block is a splitting of
the literal q-block through the canonical equal-level isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces.IntrinsicBlockLevelGroupIso

def primeBlockSplitIso {S T : Scheme} {A : Over S} [GrpObj A] [IsCommMonObj A]
    (q : ℕ) (p : A ⟶ A) [IsMonHom p] (f : T ⟶ S) {I : Type}
    (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme T I ≅ (Over.pullback f).obj (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1) p)) :
    AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme T I ≅ (Over.pullback f).obj (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q p) :=
  e ≪≫ (Over.pullback f).mapIso
    ((Grp.forget _).mapIso (Intrinsic.ActiveSubspaces.IntrinsicBlockLevelGroupIso.nativeBlockLevelGroupIso (q ^ 1) q p (pow_one q)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrimeBlockSplitting
