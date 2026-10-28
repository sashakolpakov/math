import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IsomorphismUniversalPoints

/-! # Parameter Classifier Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterClassifierFaithfulness

noncomputable section

/-! A classifier on a subparameter is injective when its underlying maps recover an injective ambient classifier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe v u

theorem parameterClassifier_injective {C : Type u} [Category.{v} C] {T W M : C}
    (i : W ⟶ M) [Mono i] {F Z : Type v} (φ : (T ⟶ M) → F) (hφ : Function.Injective φ)
    (f : (T ⟶ W) → Z) (ψ : Z → F) (h : ∀ c, ψ (f c) = φ (c ≫ i)) : Function.Injective f := by
  intro c d hcd
  apply (cancel_mono i).mp
  apply hφ
  exact (h c).symm.trans ((congrArg ψ hcd).trans (h d))

theorem boundedAbelianIsoParameter_point_injective
    {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) (T : Over S) :
    Function.Injective (fun c : T ⟶ Bounded.IsoParameters.boundedAbelianIsoParameter A B j P =>
      (Bounded.IsoParameters.boundedAbelianIsoParameterPointEquiv A B j P T c).val.val.val) := by
  intro c d h
  apply (Bounded.IsoParameters.boundedAbelianIsoParameterPointEquiv A B j P T).injective
  exact Subtype.ext (Subtype.ext (Subtype.ext h))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterClassifierFaithfulness
