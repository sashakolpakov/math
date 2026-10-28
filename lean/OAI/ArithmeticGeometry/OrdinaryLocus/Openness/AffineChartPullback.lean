import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Affine Chart Pullback -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineChartPullback.Construction

noncomputable section

/-! Finite morphisms on their canonical affine source and target charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem isPullback_affine_preimage
    {X Y : Scheme} (f : X ⟶ Y) [IsAffineHom f]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    IsPullback (hU.preimage f).fromSpec (Spec.map (f.app U)) f hU.fromSpec := by
  have h : Spec.map (f.app U) ≫ hU.fromSpec = (hU.preimage f).fromSpec ≫ f := by
    simpa only [Scheme.Hom.app_eq_appLE] using
      IsAffineOpen.SpecMap_appLE_fromSpec f hU (hU.preimage f) le_rfl
  apply (IsOpenImmersion.isPullback (Spec.map (f.app U))
    (hU.preimage f).fromSpec hU.fromSpec f h.symm ?_).flip
  simp only [IsAffineOpen.opensRange_fromSpec]

def affinePreimageIso
    {X Y : Scheme} (f : X ⟶ Y) [IsAffineHom f]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    Over.mk (Spec.map (f.app U)) ≅ (Over.pullback hU.fromSpec).obj (Over.mk f) := by
  let h := isPullback_affine_preimage f U hU
  let h' := IsPullback.of_hasPullback f hU.fromSpec
  exact Over.isoMk (h.isoIsPullback _ _ h') (h.isoIsPullback_hom_snd _ _ h')

theorem geometricPointCard_affine_preimage
    {X Y : Scheme} (f : X ⟶ Y) [IsAffineHom f]
    (U : Y.Opens) (hU : IsAffineOpen U) (t : Spec Γ(Y, U)) :
    Nat.card (DefinitionsTorsion.geometricPoint (Spec Γ(Y, U)) t ⟶
      Over.mk (Spec.map (f.app U))) =
      Nat.card (DefinitionsTorsion.geometricPoint Y (hU.fromSpec t) ⟶ Over.mk f) := by
  exact (Nat.card_congr (Iso.homCongr (Iso.refl _)
    (affinePreimageIso f U hU))).trans
      (OpenBaseChange.Construction.geometricPointCard_openBaseChange hU.fromSpec (Over.mk f) t)

theorem finrank_affine_preimage
    {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] [Flat f]
    (U : Y.Opens) (hU : IsAffineOpen U) (t : Spec Γ(Y, U)) :
    (Spec.map (f.app U)).finrank t = f.finrank (hU.fromSpec t) :=
  Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_affine_preimage f U hU) t

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineChartPullback.Construction
