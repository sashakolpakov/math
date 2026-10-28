import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.IdealGluing

/-! # Ideal Precomposition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective

noncomputable section

/-! Compatible affine projective ideals can be pulled back along every base morphism by precomposition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} {n : ℕ} (D : IdealMatching.AffineProjectiveIdealData S n) (f : T ⟶ S)

def IdealMatching.AffineProjectiveIdealData.precomp : IdealMatching.AffineProjectiveIdealData T n where
  ideal x := D.ideal (x ≫ f)
  naturality φ x := by
    rw [Category.assoc]
    exact D.naturality φ (x ≫ f)

theorem IdealMatching.AffineProjectiveIdealData.precomp_glue_comap {R : CommRingCat.{u}} (x : Spec R ⟶ T) :
    (D.precomp f).glue.comap (Charts.affineProjectiveChartMap x n) = D.ideal (x ≫ f) :=
  (D.precomp f).glue_comap x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective
