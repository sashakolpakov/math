import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalizableSubgroup
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CharacterCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks

/-! # Diagonalizable Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalizableCoordinates.CM

noncomputable section

/-! Free coordinates for the actual character group determine the
standard multiplicative model of a diagonalizable finite group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps.CM.Criterion

variable {k : Type} [Field k]
  (G : Grp (Over (Spec (.of k)))) (R : CommHopfAlgCat k) [Module.Finite k R]
  (i : (hopfSpec (.of k)).obj (.op R) ≅ G)
  (hspan : Submodule.span k (Set.range (GroupLike.val (R := k) (A := R))) = ⊤)

def multiplicativeIso (q n d : ℕ)
    (e : (G ⟶ AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))) ≃* TorsionCoordinateMaps.CM.Criterion.coordinates q n d) :
    G ≅ AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q n d := by
  let u : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n d ≃* TorsionCoordinateMaps.CM.Criterion.coordinates q n d := MulEquiv.ulift
  let a := (u.trans e.symm).trans (CharacterCoordinates.CM.coordinateCharactersEquiv k G R i)
  exact i.symm ≪≫ (hopfSpec (.of k)).mapIso
    (CommHopfAlgCat.isoMk (Picard.Homomorphisms.CharacterSpan.Construction.characterHopfEquivOfSpan k R hspan)).op ≪≫
      (hopfSpec (.of k)).mapIso (CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k a)).op

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalizableCoordinates.CM
