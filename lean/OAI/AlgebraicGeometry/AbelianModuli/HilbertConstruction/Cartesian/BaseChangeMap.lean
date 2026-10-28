import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactoredBaseRecovery
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Base Change Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.BaseChangeMap

noncomputable section

/-! Two actual Cartesian realizations over successive bases determine a unique geometric base-change map and an actual pullback isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S T U : Scheme.{u}} (f : T ⟶ U) (c : U ⟶ S)
variable {A : Over S} {X : Over T} {Y : Over U} (qX : X.left ⟶ A.left) (qY : Y.left ⟶ A.left)
variable (hX : IsPullback qX X.hom A.hom (f ≫ c)) (hY : IsPullback qY Y.hom A.hom c)

def cartesianBaseChangeMap : X.left ⟶ Y.left :=
  FactoredBaseRecovery.factoredBaseRecovery qX X.hom A.hom f c hX ≫ hY.isoPullback.inv

theorem cartesianBaseChangeMap_comp : cartesianBaseChangeMap f c qX qY hX hY ≫ qY = qX := by
  rw [cartesianBaseChangeMap, Category.assoc, hY.isoPullback_inv_fst, FactoredBaseRecovery.factoredBaseRecovery_fst]

theorem cartesianBaseChangeMap_over :
    cartesianBaseChangeMap f c qX qY hX hY ≫ Y.hom = X.hom ≫ f := by
  rw [cartesianBaseChangeMap, Category.assoc, hY.isoPullback_inv_snd, FactoredBaseRecovery.factoredBaseRecovery_snd]

theorem cartesianBaseChangeMap_unique (m : X.left ⟶ Y.left)
    (hm : m ≫ qY = qX) (hm' : m ≫ Y.hom = X.hom ≫ f) :
    m = cartesianBaseChangeMap f c qX qY hX hY := by
  apply hY.hom_ext
  · exact hm.trans (cartesianBaseChangeMap_comp f c qX qY hX hY).symm
  · exact hm'.trans (cartesianBaseChangeMap_over f c qX qY hX hY).symm

theorem cartesianBaseChangeMap_isPullback :
    IsPullback (cartesianBaseChangeMap f c qX qY hX hY) X.hom Y.hom f := by
  have hi : IsPullback hY.isoPullback.inv (pullback.snd A.hom c) Y.hom (𝟙 U) := by
    apply IsPullback.of_horiz_isIso
    exact ⟨hY.isoPullback_inv_snd.trans (Category.comp_id _).symm⟩
  have h := (FactoredBaseRecovery.factoredBaseRecovery_isPullback qX X.hom A.hom f c hX).paste_horiz hi
  simpa only [Category.comp_id, cartesianBaseChangeMap] using h

def cartesianBaseChangeOverIso : X ≅ (Over.pullback f).obj Y :=
  Over.isoMk (cartesianBaseChangeMap_isPullback f c qX qY hX hY).isoPullback
    (cartesianBaseChangeMap_isPullback f c qX qY hX hY).isoPullback_hom_snd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.BaseChangeMap
