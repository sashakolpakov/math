import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.IdealMatching

/-! # Ideal Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective

noncomputable section

/-! Effective gluing of coefficient-compatible projective ideals, with recovery on every affine base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {n : ℕ} (D : IdealMatching.AffineProjectiveIdealData S n)

def IdealMatching.AffineProjectiveIdealData.glue : (Projective.ProjectivePresentations.projectiveSpaceOver S n).left.IdealSheafData :=
  (D.matchingData S.affineOpenCover).glue

theorem IdealMatching.AffineProjectiveIdealData.glue_comap_member (i : S.affineOpenCover.I₀) :
    D.glue.comap (Charts.affineProjectiveChartMap (S.affineOpenCover.f i) n) =
      D.ideal (S.affineOpenCover.f i) :=
  (D.matchingData S.affineOpenCover).glue_comap i

theorem IdealMatching.AffineProjectiveIdealData.glue_comap {R : CommRingCat.{u}} (x : Spec R ⟶ S) :
    D.glue.comap (Charts.affineProjectiveChartMap x n) = D.ideal x := by
  let C := Projective.AffineCover.projectiveAffineOpenCover S.affineOpenCover n
  let f := Charts.affineProjectiveChartMap x n
  apply ClosedFamily.OpenEquality.ideal_eq_of_open_cover (C.pullback₁ f)
  intro i
  let a := pullback.fst f (C.f i)
  let b := pullback.snd f (C.f i)
  have hi : D.glue.comap (C.f i) = D.ideal (S.affineOpenCover.f i) := D.glue_comap_member i
  have hm : (D.ideal x).comap a = (D.ideal (S.affineOpenCover.f i)).comap b :=
    D.compatible x (S.affineOpenCover.f i) a b pullback.condition
  change (D.glue.comap f).comap a = (D.ideal x).comap a
  exact (D.glue.comap_comp a f).symm.trans
    ((congrArg (fun q => D.glue.comap q) (show a ≫ f = b ≫ C.f i from pullback.condition)).trans
      ((D.glue.comap_comp b (C.f i)).trans
        ((congrArg (fun I => I.comap b) hi).trans hm.symm)))

theorem IdealMatching.AffineProjectiveIdealData.glue_unique (I : (Projective.ProjectivePresentations.projectiveSpaceOver S n).left.IdealSheafData)
    (hI : ∀ {R : CommRingCat.{u}} (x : Spec R ⟶ S),
      I.comap (Charts.affineProjectiveChartMap x n) = D.ideal x) : I = D.glue :=
  ClosedFamily.OpenEquality.ideal_eq_of_open_cover (Projective.AffineCover.projectiveAffineOpenCover S.affineOpenCover n) I D.glue
    (fun i => (hI (S.affineOpenCover.f i)).trans (D.glue_comap_member i).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective
