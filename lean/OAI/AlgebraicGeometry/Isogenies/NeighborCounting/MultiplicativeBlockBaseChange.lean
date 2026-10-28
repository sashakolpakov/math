import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffinePullback

/-! # Multiplicative Block Base Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MultiplicativeBlockBaseChange

noncomputable section

/-! Scalar extension of the actual ordinary multiplicative block
is the same native group-algebra model over the new coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction

variable (R S : Type) [CommRing R] [CommRing S]

def multiplicativeBlockBaseChangeIso [Algebra R S] (q n d : ℕ) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj
      (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock R q n d) ≅ AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock S q n d :=
  AbelianScheme.CartierDuality.AffinePullback.Construction.affineHopfPullbackIso R S (MonoidAlgebra R (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n d)) ≪≫
    ((hopfSpec (CommRingCat.of S)).mapIso
      (CommHopfAlgCat.isoMk
        (AbelianScheme.CartierDuality.AffinePullback.Construction.monoidAlgebraBaseChangeBialgEquiv R S (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n d))).op).symm

def multiplicativeBlockRingHomBaseChangeIso (f : R →+* S) (q n d : ℕ) :
    (Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.obj
      (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock R q n d) ≅ AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock S q n d := by
  let : Algebra R S := f.toAlgebra
  exact multiplicativeBlockBaseChangeIso R S q n d

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MultiplicativeBlockBaseChange
