import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.CoordinateBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.Charts

/-! # Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual affine pullbacks of closed families in relative projective space and compatibility with coefficient extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {T : Scheme.{u}} {n : ℕ} (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver T n))
variable {R A : CommRingCat.{u}} (x : Spec R ⟶ T)

def Closed.Families.FlatClosedFamily.affineProjectivePullback : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n) :=
  F.pullbackAlong (AffineProjective.Charts.affineProjectiveChartMap x n) x (AffineProjective.Charts.affineProjectiveChartMap_isPullback x n)

theorem Closed.Families.FlatClosedFamily.affineProjectivePullback_coefficient (φ : R ⟶ A) :
    F.affineProjectivePullback (Spec.map φ ≫ x) =
      (F.affineProjectivePullback x).pullbackAlong (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n)
        (Spec.map φ) (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback φ n) := by
  apply Closed.Families.FlatClosedFamily.ext
  change F.ideal.comap (AffineProjective.Charts.affineProjectiveChartMap (Spec.map φ ≫ x) n) =
    (F.ideal.comap (AffineProjective.Charts.affineProjectiveChartMap x n)).comap (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n)
  exact (congrArg (fun p => F.ideal.comap p) (AffineProjective.Charts.affineProjectiveChartMap_naturality φ x n).symm).trans
    (F.ideal.comap_comp _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
