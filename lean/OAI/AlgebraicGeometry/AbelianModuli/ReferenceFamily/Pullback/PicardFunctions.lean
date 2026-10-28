import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PicardFunctions

/-! # Picard Functions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.PicardFunctions

noncomputable section

/-! Every further parameter product of an arbitrary pullback of a
locally noetherian abelian family has exactly the parameter's functions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem pullbackFamily_product_app_isIso {X S : Scheme.{0}} [IsLocallyNoetherian X]
    {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g X) (f : S ⟶ X) (V : Over S) (U : V.left.Opens) :
    IsIso ((fst V (A.pullback f).scheme).left.app U) := by
  let B := A.pullback f
  have h₁ : IsPullback (snd V B.scheme).left (fst V B.scheme).left B.scheme.hom V.hom :=
    (IsPullback.of_hasPullback V.hom B.scheme.hom).flip
  have h₂ : IsPullback (CategoryTheory.Limits.pullback.fst A.scheme.hom f) B.scheme.hom A.scheme.hom f :=
    IsPullback.of_hasPullback A.scheme.hom f
  exact Abelian.BaseChangeFunctionSheaf.abelian_baseChange_function_app_isIso A
    ((snd V B.scheme).left ≫ CategoryTheory.Limits.pullback.fst A.scheme.hom f)
    (fst V B.scheme).left (V.hom ≫ f) (h₁.paste_horiz h₂) U

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.PicardFunctions
