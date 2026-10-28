import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairOrdinaryForms
import OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectedCechTotal

/-! # Pair Ordinary Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairOrdinaryPullback.AffinePairOrdinaryPullback

noncomputable section

/-! The original ordinary algebraic comparison on affine pairs
uses exactly geometric de Rham pullback to the actual smaller opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

def openMap : PairOrdinaryForms.AffinePairOrdinaryForms.sourceOpens R f ⟶
    PairOrdinaryForms.AffinePairOrdinaryForms.targetOpens R f ⋙ Cech.Image.CechImage.preimage f.left where
  app U := homOfLE U.property
  naturality _ _ _ := Subsingleton.elim _ _

theorem coordinates : PairOrdinaryForms.AffinePairOrdinaryForms.map R f =
    ProjectedCechTotal.ProjectedCechComplexPullback.pairedMap R f.left
      (PairOrdinaryForms.AffinePairOrdinaryForms.targetOpens R f) (PairOrdinaryForms.AffinePairOrdinaryForms.sourceOpens R f)
      (openMap R f) (DeRham.Int.presheafPullback f) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext U
  exact PairOrdinaryForms.AffinePairOrdinaryForms.original_pullback R f q U

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairOrdinaryPullback.AffinePairOrdinaryPullback
