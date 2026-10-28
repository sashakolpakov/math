import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientDescentCompatibility

/-! # Coefficient Base Change Associativity -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientBaseChangeAssociativity

noncomputable section

/-! A coefficient ideal for a composite affine base change also represents
the same condition on the iterated pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem affineIdealCoefficient_iterated_baseChange
    {R A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) [Flat f]
    (K : X.IdealSheafData) (φ : R ⟶ A) (ψ : A ⟶ B) (I : Ideal B)
    (hI : Affine.IdealCoefficientTests.IsAffineIdealCoefficient B (pullback.snd f (Spec.map (φ ≫ ψ)))
      (K.comap (pullback.fst f (Spec.map (φ ≫ ψ)))) I) :
    Affine.IdealCoefficientTests.IsAffineIdealCoefficient B
      (pullback.snd (pullback.snd f (Spec.map φ)) (Spec.map ψ))
      ((K.comap (pullback.fst f (Spec.map φ))).comap
        (pullback.fst (pullback.snd f (Spec.map φ)) (Spec.map ψ))) I := by
  apply Affine.IdealCoefficientTests.affineIdealCoefficient_of_tests
  intro C τ
  rw [Presentations.Ideal.PullbackVanishing.pullback_ideal_vanishing_comp, ← Spec.map_comp,
    Presentations.Ideal.PullbackVanishing.pullback_ideal_vanishing_comp, ← Spec.map_comp, ← Category.assoc]
  exact CoefficientDescentCompatibility.affineIdealCoefficient_test_composite f K (φ ≫ ψ) I hI τ

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientBaseChangeAssociativity
