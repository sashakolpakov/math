import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BaseChangeIsoProjections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Spec Iso Projections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpecIsoProjections

noncomputable section

/-! The affine-base comparison already used by projective presentations
preserves the coefficient projection. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false

def polynomialProjectiveMapIso {R A : CommRingCat.{u}} (e : R ≅ A) (n : ℕ) :
    (ProjectivePresentations.affineProjectiveSpace A n).left ≅ (ProjectivePresentations.affineProjectiveSpace R n).left where
  hom := CoefficientFunctoriality.polynomialProjectiveMap e.hom n
  inv := CoefficientFunctoriality.polynomialProjectiveMap e.inv n
  hom_inv_id := by rw [← CoefficientFunctoriality.polynomialProjectiveMap_comp, e.inv_hom_id, CoefficientFunctoriality.polynomialProjectiveMap_id]
  inv_hom_id := by rw [← CoefficientFunctoriality.polynomialProjectiveMap_comp, e.hom_inv_id, CoefficientFunctoriality.polynomialProjectiveMap_id]

theorem equalBasePullback_inv_fst {S T : Scheme.{u}} (A : Over S)
    (f g : T ⟶ S) (h : f = g) :
    (eqToIso (congrArg (fun b => (Over.pullback b).obj A) h)).inv.left ≫ pullback.fst A.hom f =
      pullback.fst A.hom g :=
  (((Over.forget T).mapIso (eqToIso (congrArg (fun b => (Over.pullback b).obj A) h))).inv_comp_eq).mpr
    (EqualBasePullbackProjections.equalBasePullback_hom_fst A f g h).symm

private theorem over_trans_inv_left_comp {S : Scheme.{u}} {X Y Z : Over S} {W : Scheme.{u}}
    (e : X ≅ Y) (f : Y ≅ Z) (p : X.left ⟶ W) (q : Y.left ⟶ W) (r : Z.left ⟶ W)
    (he : e.inv.left ≫ p = q) (hf : f.inv.left ≫ q = r) :
    (e ≪≫ f).inv.left ≫ p = r := by
  change (f.inv.left ≫ e.inv.left) ≫ p = r
  rw [Category.assoc, he, hf]

private theorem changed_base_inv_fst {S T : Scheme.{u}} (P : Over S)
    (f g : T ⟶ S) (h : f = g) {Q : Over T}
    (a : Q ≅ (Over.pullback g).obj P) :
    ((eqToIso (congrArg (fun b => (Over.pullback b).obj P) h)) ≪≫ a.symm).inv.left ≫
      pullback.fst P.hom f = a.hom.left ≫ pullback.fst P.hom g :=
  over_trans_inv_left_comp _ a.symm _ _ _ (equalBasePullback_inv_fst P f g h) rfl

theorem projectiveSpaceOverSpecIso_inv_coefficients (R : CommRingCat.{u}) (n : ℕ) :
    (SpaceBaseChange.projectiveSpaceOverSpecIso R n).inv.left ≫ RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection (Spec R) n =
      CoefficientFunctoriality.polynomialProjectiveMap (Scheme.ΓSpecIso R).hom n := by
  let : Algebra Γ(Spec R, ⊤) R := (Scheme.ΓSpecIso R).hom.hom.toAlgebra
  let P := ProjectivePresentations.affineProjectiveSpace Γ(Spec R, ⊤) n
  let a := SpaceBaseChange.affineProjectiveSpaceBaseChangeIso (R := Γ(Spec R, ⊤)) (A := R) n
  have h := changed_base_inv_fst P _ _ (SpecMap_ΓSpecIso_hom R).symm a
  exact h.trans (SpaceBaseChange.affineProjectiveSpaceBaseChangeIso_hom_fst (R := Γ(Spec R, ⊤)) (A := R) n)

/-- The composite target comparison appearing in the existing product presentation. -/
def projectiveCoefficientReturnIso (S : Scheme.{u}) (n : ℕ) :
    ProjectivePresentations.projectiveSpaceOver S n ≅ ProjectivePresentations.projectiveSpaceOver S n :=
  (PresentationBaseChange.nativeAffineProjectivePresentation Γ(S, ⊤) n).baseChangeIso S.toSpecΓ

theorem projectiveCoefficientReturnIso_hom_coefficients (S : Scheme.{u}) (n : ℕ) :
    (projectiveCoefficientReturnIso S n).hom.left ≫ RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n =
      RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n := by
  let e := Scheme.ΓSpecIso Γ(S, ⊤)
  let a := CoefficientFunctoriality.polynomialProjectiveMap e.hom n
  let : IsIso a := inferInstanceAs (IsIso (polynomialProjectiveMapIso e n).hom)
  let j := (SpaceBaseChange.projectiveSpaceOverSpecIso Γ(S, ⊤) n).inv
  let b := (SpaceBaseChange.projectiveSpaceOverBaseChangeIso S.toSpecΓ n).inv.left
  let k := ((Over.pullback S.toSpecΓ).map j).left
  let q := RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n
  let q' := RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection (Spec Γ(S, ⊤)) n
  have hbase : RelativeProjective.BaseMaps.relativeProjectiveBaseMap S.toSpecΓ n ≫ q' = q ≫ a := by
    have h := RelativeProjective.BaseMaps.relativeProjectiveBaseMap_fst S.toSpecΓ n
    rw [Scheme.toSpecΓ_appTop] at h
    exact h
  apply (cancel_mono a).mp
  change ((k ≫ b) ≫ q) ≫ a = q ≫ a
  calc
    _ = k ≫ b ≫ (q ≫ a) := by simp only [Category.assoc]
    _ = k ≫ b ≫ (RelativeProjective.BaseMaps.relativeProjectiveBaseMap S.toSpecΓ n ≫ q') :=
      congrArg (fun v => k ≫ b ≫ v) hbase.symm
    _ = (k ≫ pullback.fst (ProjectivePresentations.projectiveSpaceOver (Spec Γ(S, ⊤)) n).hom S.toSpecΓ) ≫ q' := by
      rw [← Category.assoc b, BaseChangeIsoProjections.projectiveSpaceOverBaseChangeIso_inv_baseMap]
      exact (Category.assoc _ _ _).symm
    _ = (q ≫ j.left) ≫ q' := congrArg (fun v => v ≫ q') (Pullback.Comparisons.overPullback_map_left_fst j S.toSpecΓ)
    _ = q ≫ a := by rw [Category.assoc, projectiveSpaceOverSpecIso_inv_coefficients]

theorem projectiveCoefficientReturnIso_hom (S : Scheme.{u}) (n : ℕ) :
    (projectiveCoefficientReturnIso S n).hom = 𝟙 (ProjectivePresentations.projectiveSpaceOver S n) := by
  apply Over.OverMorphism.ext
  apply (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_isPullback S n).hom_ext
  · exact (projectiveCoefficientReturnIso_hom_coefficients S n).trans (Category.id_comp _).symm
  · exact (projectiveCoefficientReturnIso S n).hom.w.trans (Category.id_comp _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpecIsoProjections
