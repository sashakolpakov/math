import OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedCoefficientModels
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.CommonStage

/-! # Fixed Coefficient Diagrams -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedCoefficientDiagrams

noncomputable section

/-! One finite coefficient stage for a diagram between specified models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem finite_morphisms_between_fixed_coefficient_models_descend
    {R F : Type} [CommRing R] [Field F] [Algebra R F]
    {I J : Type*} [Finite J] (src dst : J → I)
    (X : I → Over (Spec (.of R))) (G : I → Over (Spec (.of F)))
    (hX : ∀ i, ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (X i).hom)
    (p : ∀ i, (G i).left ⟶ (X i).left)
    (hp : ∀ i, IsPullback (p i) (G i).hom (X i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R F))))
    (a : ∀ j, G (src j) ⟶ G (dst j)) :
    ∃ (t : Finset F)
      (b : ∀ j, (Over.pullback (EmptyCoefficientBase.coefficientStructureMap t)).obj (X (src j)) ⟶
        (Over.pullback (EmptyCoefficientBase.coefficientStructureMap t)).obj (X (dst j))),
      ∀ j, FixedCoefficientModels.fixedCoefficientProjection (X (src j)) (p (src j)) (hp (src j)) t ≫ (b j).left =
        (a j).left ≫ FixedCoefficientModels.fixedCoefficientProjection (X (dst j)) (p (dst j)) (hp (dst j)) t := by
  let X₀ i := (Over.pullback (EmptyCoefficientBase.coefficientStructureMap (R := R) (F := F) ∅)).obj (X i)
  obtain ⟨t, h, b, hb⟩ := IntegralModel.Coefficient.CommonStage.Coefficients.finite_morphisms_descend src dst G X₀
    (fun i => FixedCoefficientModels.fixedCoefficientModel_finitePresentation (X i) (hX i) ∅)
    (fun i => FixedCoefficientModels.fixedCoefficientProjection (X i) (p i) (hp i) ∅)
    (fun i => FixedCoefficientModels.fixedCoefficientProjection_cartesian (X i) (p i) (hp i) ∅) a
  refine ⟨t, fun j => (FixedCoefficientModels.fixedCoefficientEnlargementIso (X (src j)) h).inv ≫ b j ≫
    (FixedCoefficientModels.fixedCoefficientEnlargementIso (X (dst j)) h).hom, ?_⟩
  intro j
  change FixedCoefficientModels.fixedCoefficientProjection (X (src j)) (p (src j)) (hp (src j)) t ≫
      ((FixedCoefficientModels.fixedCoefficientEnlargementIso (X (src j)) h).inv.left ≫
        ((b j).left ≫ (FixedCoefficientModels.fixedCoefficientEnlargementIso (X (dst j)) h).hom.left)) = _
  rw [← Category.assoc, FixedCoefficientModels.fixedCoefficientProjection_enlarge_inv,
    ← Category.assoc, hb, Category.assoc, FixedCoefficientModels.fixedCoefficientProjection_enlarge]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedCoefficientDiagrams
