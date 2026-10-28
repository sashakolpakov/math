import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AffineBaseChangeConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FunctionSheafAffineCriterion

/-! # Field Base Change Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeConstants

noncomputable section

/-! A pointed connected reduced proper scheme over a field has only base functions
after arbitrary base change, including nonreduced test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X Y P : Scheme.{u}}

theorem properField_baseChange_function_app_isIso
    (p : X ⟶ Spec (.of K)) [UniversallyClosed p] [IsSeparated p]
    [IsReduced X] [ConnectedSpace X] (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)
    {a : P ⟶ X} {b : P ⟶ Y} {g : Y ⟶ Spec (.of K)} (H : IsPullback a b p g)
    (U : Y.Opens) : IsIso (b.app U) := by
  apply FunctionSheafAffineCriterion.function_app_isIso_of_affine b
  intro V hV
  let : IsAffine V.toScheme := hV
  have H' : IsPullback ((b ⁻¹ᵁ V).ι ≫ a) (b ∣_ V) p (V.ι ≫ g) :=
    (isPullback_morphismRestrict b V).flip.paste_horiz H
  exact (FunctionSheafAffineCriterion.morphismRestrict_appTop_isIso_iff b V).mp
    (AffineBaseChangeConstants.properField_affineBaseChange_globalFunctions_isIso p x hx H')

theorem properField_baseChange_globalFunctions_isIso
    (p : X ⟶ Spec (.of K)) [UniversallyClosed p] [IsSeparated p]
    [IsReduced X] [ConnectedSpace X] (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)
    {a : P ⟶ X} {b : P ⟶ Y} {g : Y ⟶ Spec (.of K)} (H : IsPullback a b p g) :
    IsIso b.appTop := properField_baseChange_function_app_isIso p x hx H ⊤

theorem section_globalFunctions_isIso (b : P ⟶ Y) [IsIso b.appTop]
    (σ : Y ⟶ P) (hσ : σ ≫ b = 𝟙 _) : IsIso σ.appTop := by
  have h : b.appTop ≫ σ.appTop = 𝟙 _ :=
    (Scheme.Hom.comp_appTop σ b).symm.trans
      ((congrArg Scheme.Hom.appTop hσ).trans Scheme.Hom.id_appTop)
  have : IsIso (b.appTop ≫ σ.appTop) := h.symm ▸ inferInstanceAs (IsIso (𝟙 Γ(Y, ⊤)))
  exact IsIso.of_isIso_comp_left b.appTop σ.appTop

theorem properField_baseChangedSection_globalFunctions_isIso
    (p : X ⟶ Spec (.of K)) [UniversallyClosed p] [IsSeparated p]
    [IsReduced X] [ConnectedSpace X] (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)
    {a : P ⟶ X} {b : P ⟶ Y} {g : Y ⟶ Spec (.of K)} (H : IsPullback a b p g)
    (σ : Y ⟶ P) (hσ : σ ≫ b = 𝟙 _) : IsIso σ.appTop := by
  have : IsIso b.appTop := properField_baseChange_globalFunctions_isIso p x hx H
  exact section_globalFunctions_isIso b σ hσ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeConstants
