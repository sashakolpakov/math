import OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.SinglePresheafCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafSingleIndexedCoordinates

/-! # Single Presheaf Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SinglePresheafCoordinates

noncomputable section

/-! The original principal single/sheaf coordinates factor the exact
change to the literal presheaf single complex used by the cover formula. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) (c : ℕ) {ι : Type u} [LinearOrder ι]
  (W : ι → SectionPresheaf.Index U)

def lastBicomplexIso :=
  ((AugmentedOrdered.CechFunctor.functor W).mapHomologicalComplex (.up ℕ)).mapIso
    (((AugmentedCech.AmbientTotal.restriction (AdditiveSections.opens U hU)).mapHomologicalComplex
      (.up ℕ)).mapIso (Reference.SinglePresheafCoordinates.lastIso N c))

def lastTotalIso := HomologicalComplex₂.total.mapIso (lastBicomplexIso U hU N c W) (.up ℕ)

def homologyIso (q : ℕ) :=
  SingleAdditiveSections.homologyIso U hU N c W q ≪≫
    homologyMapIso (lastTotalIso U hU N c W) q

theorem factor (q : ℕ) :
    (AdditiveSections.homologyIso U hU
      (Reference.SinglePresheafCoordinates.moduleSingle N c) W q).hom ≫
      homologyMap (PresheafCover.Comparison.totalMap
        (AdditiveSections.opens U hU) W
        (Reference.SinglePresheafCoordinates.iso N c).hom) q =
    (homologyIso U hU N c W q).hom := by
  simp only [homologyIso, SingleAdditiveSections.homologyIso,
    Reference.SinglePresheafCoordinates.iso, Iso.trans_hom, homologyMapIso_hom,
    PresheafCover.Comparison.totalMap, Functor.map_comp,
    HomologicalComplex₂.total.map_comp, homologyMap_comp, Category.assoc]
  rfl

def coordinates (g q : ℕ) (hq : q=g+c) :=
  homologyIso U hU N c W q ≪≫
    PresheafSingleIndexedCoordinates.sourceIso
      (Reference.SinglePresheafCoordinates.presheaf N) c g
      (AdditiveSections.opens U hU) W q hq

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SinglePresheafCoordinates
