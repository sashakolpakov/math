import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.PointLifts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.AffineCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdealOpenMatching

/-! # Ideal Matching -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.IdealMatching

noncomputable section

/-! Coefficient-compatible ideals on affine projective spaces agree on all overlaps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

structure AffineProjectiveIdealData (S : Scheme.{u}) (n : ℕ) where
  ideal : ∀ {R : CommRingCat.{u}}, (Spec R ⟶ S) → (Projective.ProjectivePresentations.affineProjectiveSpace R n).left.IdealSheafData
  naturality : ∀ {R A : CommRingCat.{u}} (φ : R ⟶ A) (x : Spec R ⟶ S),
    ideal (Spec.map φ ≫ x) = (ideal x).comap (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n)

namespace AffineProjectiveIdealData

variable {S : Scheme.{u}} {n : ℕ} (D : AffineProjectiveIdealData S n)

theorem point_ideal {R A : CommRingCat.{u}} (x : Spec R ⟶ S)
    (a : Spec A ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R n).left) :
    (D.ideal x).comap a =
      (D.ideal (Spec.map (PointLifts.affineProjectivePointCoefficients a) ≫ x)).comap
        (PointLifts.affineProjectivePointLift a) :=
  (congrArg (fun f => (D.ideal x).comap f) (PointLifts.affineProjectivePointLift_map a).symm).trans
    (((D.ideal x).comap_comp _ _).trans
      (congrArg (fun I => I.comap (PointLifts.affineProjectivePointLift a))
        (D.naturality (PointLifts.affineProjectivePointCoefficients a) x).symm))

theorem affine_compatible {R Q A : CommRingCat.{u}} (x : Spec R ⟶ S) (y : Spec Q ⟶ S)
    (a : Spec A ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R n).left)
    (b : Spec A ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace Q n).left)
    (h : a ≫ Charts.affineProjectiveChartMap x n = b ≫ Charts.affineProjectiveChartMap y n) :
    (D.ideal x).comap a = (D.ideal y).comap b := by
  let φ := PointLifts.affineProjectivePointCoefficients a
  let ψ := PointLifts.affineProjectivePointCoefficients b
  have hy : Spec.map φ ≫ x = Spec.map ψ ≫ y := by
    calc
      Spec.map φ ≫ x = (a ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom) ≫ x :=
        congrArg (fun f => f ≫ x) (PointLifts.affineProjectivePointCoefficients_spec a)
      _ = (a ≫ Charts.affineProjectiveChartMap x n) ≫ (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom := by
        simp only [Category.assoc, Charts.affineProjectiveChartMap_over]
      _ = (b ≫ Charts.affineProjectiveChartMap y n) ≫ (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom :=
        congrArg (fun f => f ≫ (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom) h
      _ = (b ≫ (Projective.ProjectivePresentations.affineProjectiveSpace Q n).hom) ≫ y := by
        simp only [Category.assoc, Charts.affineProjectiveChartMap_over]
      _ = Spec.map ψ ≫ y :=
        congrArg (fun f => f ≫ y) (PointLifts.affineProjectivePointCoefficients_spec b).symm
  have hz : PointLifts.affineProjectivePointLift a = PointLifts.affineProjectivePointLift b := by
    apply (Charts.affineProjectiveChartMap_isPullback (Spec.map φ ≫ x) n).hom_ext
    · exact (PointLifts.affineProjectivePointLift_chart a x).trans
        (h.trans ((PointLifts.affineProjectivePointLift_chart b y).symm.trans
          (congrArg (fun f => PointLifts.affineProjectivePointLift b ≫ Charts.affineProjectiveChartMap f n) hy.symm)))
    · exact (PointLifts.affineProjectivePointLift_over a).trans (PointLifts.affineProjectivePointLift_over b).symm
  rw [D.point_ideal x a, D.point_ideal y b]
  change (D.ideal (Spec.map φ ≫ x)).comap (PointLifts.affineProjectivePointLift a) =
    (D.ideal (Spec.map ψ ≫ y)).comap (PointLifts.affineProjectivePointLift b)
  rw [hy, hz]

theorem compatible {R Q : CommRingCat.{u}} {W : Scheme.{u}}
    (x : Spec R ⟶ S) (y : Spec Q ⟶ S)
    (a : W ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R n).left)
    (b : W ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace Q n).left)
    (h : a ≫ Charts.affineProjectiveChartMap x n = b ≫ Charts.affineProjectiveChartMap y n) :
    (D.ideal x).comap a = (D.ideal y).comap b := by
  apply ClosedFamily.OpenEquality.ideal_eq_of_open_cover W.affineOpenCover.openCover
  intro i
  exact ((D.ideal x).comap_comp (W.affineOpenCover.f i) a).symm.trans
    ((D.affine_compatible x y (W.affineOpenCover.f i ≫ a) (W.affineOpenCover.f i ≫ b)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => W.affineOpenCover.f i ≫ f) h).trans (Category.assoc _ _ _).symm))).trans
      ((D.ideal y).comap_comp (W.affineOpenCover.f i) b))

def matchingData (C : S.AffineOpenCover) : IdealOpenMatching.IdealOpenMatchingData (Projective.AffineCover.projectiveAffineOpenCover C n) where
  ideal i := D.ideal (C.f i)
  compatible i j a b h := D.compatible (C.f i) (C.f j) a b h

end AffineProjectiveIdealData

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.IdealMatching
