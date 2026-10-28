import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverMorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ComparisonIso

/-! # Common Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CommonRecovery

noncomputable section

/-! Cartesian recovery is preserved by the coordinate-algebra presentation of an affine scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
variable (X : Over (Spec (.of C))) [IsAffine X.left]

theorem affineOver_common_recovery_isPullback {P : Scheme.{u}}
    (q : P ⟶ X.left) (p : P ⟶ Spec (.of R))
    (h : IsPullback q p X.hom (Spec.map (CommRingCat.ofHom (algebraMap C R)))) :
    IsPullback (q ≫ (OverChartPoints.affineOverIso C X).hom.left) p
      (Spec.map (CommRingCat.ofHom (algebraMap C (OverChartPoints.affineOverAlgebra C X))))
      (Spec.map (CommRingCat.ofHom (algebraMap C R))) := by
  let e := OverChartPoints.affineOverIso C X
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have he : IsPullback e.hom.left X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap C (OverChartPoints.affineOverAlgebra C X))))
      (𝟙 (Spec (.of C))) :=
    IsPullback.of_horiz_isIso ⟨e.hom.w.trans (Category.comp_id _).symm⟩
  exact (congrArg (fun b => IsPullback (q ≫ e.hom.left) p
    (Spec.map (CommRingCat.ofHom (algebraMap C (OverChartPoints.affineOverAlgebra C X)))) b)
    (Category.comp_id _)).mp (h.paste_horiz he)

theorem affineOver_common_recovery_natural
    {Y : Over (Spec (.of C))} [IsAffine Y.left] (f : X ⟶ Y)
    {P : Scheme.{u}} (qX : P ⟶ X.left) (qY : P ⟶ Y.left) (hq : qX ≫ f.left = qY) :
    (qX ≫ (OverChartPoints.affineOverIso C X).hom.left) ≫
      Spec.map (CommRingCat.ofHom (OverMorphisms.affineOverMap C f).toRingHom) =
      qY ≫ (OverChartPoints.affineOverIso C Y).hom.left := by
  let e : X.left ⟶ Spec (.of (OverChartPoints.affineOverAlgebra C X)) := (OverChartPoints.affineOverIso C X).hom.left
  let d : Spec (.of (OverChartPoints.affineOverAlgebra C X)) ⟶ X.left := (OverChartPoints.affineOverIso C X).inv.left
  let e' : Y.left ⟶ Spec (.of (OverChartPoints.affineOverAlgebra C Y)) := (OverChartPoints.affineOverIso C Y).hom.left
  have he : e ≫ d = 𝟙 X.left := congrArg (fun k => k.left) (OverChartPoints.affineOverIso C X).hom_inv_id
  have hf : Spec.map (CommRingCat.ofHom (OverMorphisms.affineOverMap C f).toRingHom) = d ≫ f.left ≫ e' :=
    OverMorphisms.affineOverMap_spec C f
  change (qX ≫ e) ≫ Spec.map (CommRingCat.ofHom (OverMorphisms.affineOverMap C f).toRingHom) = qY ≫ e'
  have heq : (qX ≫ e) ≫ d = qX := by rw [Category.assoc, he, Category.comp_id]
  rw [hf]
  simp only [← Category.assoc, heq, hq]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CommonRecovery
