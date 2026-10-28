import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.Charts

/-! # Point Lifts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.PointLifts

noncomputable section

/-! An affine point of a projective chart lifts to projective space over its own coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R A : CommRingCat.{u}} {n : ℕ}

def affineProjectivePointCoefficients (a : Spec A ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R n).left) : R ⟶ A :=
  (Spec.fullyFaithful.preimage (a ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom)).unop

theorem affineProjectivePointCoefficients_spec (a : Spec A ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R n).left) :
    Spec.map (affineProjectivePointCoefficients a) = a ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom :=
  Spec.fullyFaithful.map_preimage _

def affineProjectivePointLift (a : Spec A ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R n).left) :
    Spec A ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace A n).left :=
  (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback (affineProjectivePointCoefficients a) n).lift a (𝟙 _) (by
    rw [Category.id_comp, affineProjectivePointCoefficients_spec])

theorem affineProjectivePointLift_map (a : Spec A ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R n).left) :
    affineProjectivePointLift a ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap (affineProjectivePointCoefficients a) n = a :=
  (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback (affineProjectivePointCoefficients a) n).lift_fst _ _ _

theorem affineProjectivePointLift_over (a : Spec A ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R n).left) :
    affineProjectivePointLift a ≫ (Projective.ProjectivePresentations.affineProjectiveSpace A n).hom = 𝟙 _ :=
  (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback (affineProjectivePointCoefficients a) n).lift_snd _ _ _

theorem affineProjectivePointLift_chart {S : Scheme.{u}}
    (a : Spec A ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R n).left) (x : Spec R ⟶ S) :
    affineProjectivePointLift a ≫
      Charts.affineProjectiveChartMap (Spec.map (affineProjectivePointCoefficients a) ≫ x) n =
        a ≫ Charts.affineProjectiveChartMap x n := by
  rw [← Charts.affineProjectiveChartMap_naturality, ← Category.assoc, affineProjectivePointLift_map]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.PointLifts
