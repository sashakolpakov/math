import OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedArithmeticDiagrams
import OAI.AlgebraicGeometry.PELModuli.CMPoints.GroupMapReflection

/-! # Generic Projection Maps -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.GenericProjectionMaps

noncomputable section

section

/-! A supplied generic projection determines morphisms on smooth models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem smooth_hom_eq_of_generic_projection
    {S T : Scheme} [IsReduced S] [IsLocallyNoetherian S]
    (u : T ⟶ S) [IsDominant u] {X Y : Over S}
    [Smooth X.hom] [IsSeparated Y.hom]
    {G : Over T} (p : G.left ⟶ X.left)
    (hp : IsPullback p G.hom X.hom u) (f h : X ⟶ Y)
    (heq : p ≫ f.left = p ≫ h.left) : f = h := by
  let : GeometricallyReduced X.hom := IntegralModel.GenericIdentities.geometricallyReduced_of_smooth X.hom
  let : IsReduced X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian X.hom
  let : IsDominant (pullback.fst X.hom u) := IntegralModel.GenericIdentities.base_change_projection_dominant u X
  have he : p = hp.isoPullback.hom ≫ pullback.fst X.hom u := hp.isoPullback_hom_fst.symm
  let : IsDominant p := by rw [he]; infer_instance
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated Y.hom (f.w.trans h.w.symm) p heq

theorem arithmeticModelProjection_cartesian
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : IntegralModel.Base.ArithmeticBaseExtension K κ) (X : Over B.base)
    {G : Over (Spec (.of B.extension.carrier))} (p : G.left ⟶ X.left)
    (hp : IsPullback p G.hom X.hom B.generic)
    (D : ℕ) (hD : D ≠ 0) (hdiv : B.denominator ∣ D) :
    IsPullback (FixedArithmeticDiagrams.arithmeticModelProjection B X p hp.w D hD hdiv) G.hom
      ((Over.pullback (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv)).obj X).hom
      (B.withDenominator D hD).generic := by
  apply ModelLifts.modelLift_cartesian
  rw [ArithmeticBaseMaps.arithmeticEnlargement_generic]
  exact hp

end

/-! Convert compatibility with actual generic projections into the
corresponding over-category base-change comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem generic_map_of_projection_comparison
    {S T : Scheme} (u : T ⟶ S) {X Y : Over S} {G H : Over T}
    (eX : (Over.pullback u).obj X ≅ G) (eY : (Over.pullback u).obj Y ≅ H)
    (f : X ⟶ Y) (a : G ⟶ H)
    (hc : (eX.inv.left ≫ pullback.fst X.hom u) ≫ f.left =
      a.left ≫ (eY.inv.left ≫ pullback.fst Y.hom u)) :
    (Over.pullback u).map f ≫ eY.hom = eX.hom ≫ a := by
  apply (eY.eq_comp_inv).mp
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have h := congrArg (fun k => eX.hom.left ≫ k) hc
    simp only [Category.assoc, Over.hom_left_inv_left_assoc] at h
    exact (AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst f u).trans
      (h.trans (Category.assoc _ _ _).symm)
  · change ((Over.pullback u).map f).left ≫ ((Over.pullback u).obj Y).hom =
      ((eX.hom ≫ a) ≫ eY.inv).left ≫ ((Over.pullback u).obj Y).hom
    exact ((Over.pullback u).map f).w.trans (((eX.hom ≫ a) ≫ eY.inv).w).symm

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
  (B : IntegralModel.Base.ArithmeticBaseExtension K κ) (X : Over B.base)
  (D : ℕ) (hD : D ≠ 0) (hdiv : B.denominator ∣ D)

def arithmeticGenericComparison :
    (Over.pullback (B.withDenominator D hD).generic).obj
      ((Over.pullback (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv)).obj X) ≅
        (Over.pullback B.generic).obj X :=
  IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv)
    (B.withDenominator D hD).generic B.generic (ArithmeticBaseMaps.arithmeticEnlargement_generic B D hD hdiv)

theorem arithmeticGenericComparison_projection :
    (arithmeticGenericComparison B X D hD hdiv).inv.left ≫
      pullback.fst ((Over.pullback (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv)).obj X).hom
        (B.withDenominator D hD).generic =
      FixedArithmeticDiagrams.arithmeticModelProjection B X (G := (Over.pullback B.generic).obj X) (pullback.fst X.hom B.generic)
        (IsPullback.of_hasPullback X.hom B.generic).w D hD hdiv := by
  let e := arithmeticGenericComparison B X D hD hdiv
  let u := ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv
  let v := (B.withDenominator D hD).generic
  apply pullback.hom_ext
  · rw [Category.assoc, FixedArithmeticDiagrams.arithmeticModelProjection_fst]
    have he : e.hom.left ≫ pullback.fst X.hom B.generic =
      pullback.fst (pullback.snd X.hom u) v ≫ pullback.fst X.hom u :=
      IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_fst X u v B.generic _
    exact (((Over.forget _).mapIso e).inv_comp_eq).mpr he.symm
  · rw [Category.assoc]
    change e.inv.left ≫ (pullback.fst (pullback.snd X.hom u) v ≫ pullback.snd X.hom u) = _
    rw [pullback.condition]
    change e.inv.left ≫ (((Over.pullback v).obj ((Over.pullback u).obj X)).hom ≫ v) = _
    rw [← Category.assoc, e.inv.w]
    exact (FixedArithmeticDiagrams.arithmeticModelProjection_snd B X (G := (Over.pullback B.generic).obj X)
      (pullback.fst X.hom B.generic)
      (IsPullback.of_hasPullback X.hom B.generic).w D hD hdiv).symm

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.GenericProjectionMaps
