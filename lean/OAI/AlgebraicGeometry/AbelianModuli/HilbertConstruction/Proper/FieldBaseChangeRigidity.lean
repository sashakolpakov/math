import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsRigidity

/-! # Field Base Change Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeRigidity

noncomputable section

/-! Proper connected reduced schemes over a field retain rigidity after nonreduced base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X P T Y : Scheme.{u}}

theorem properField_baseChange_restriction_globalFunctions_isIso
    (p : X ⟶ Spec (.of K)) [UniversallyClosed p] [IsSeparated p]
    [IsReduced X] [ConnectedSpace X] (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)
    {a : P ⟶ X} {b : P ⟶ T} {t : T ⟶ Spec (.of K)} (H : IsPullback a b p t)
    (V : T.Opens) : IsIso (b ∣_ V).appTop :=
  FieldBaseChangeConstants.properField_baseChange_globalFunctions_isIso p x hx
    ((isPullback_morphismRestrict b V).flip.paste_horiz H)

theorem properField_baseChange_localRigidity
    (p : X ⟶ Spec (.of K)) [UniversallyClosed p] [IsSeparated p]
    [IsReduced X] [ConnectedSpace X] (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)
    {a : P ⟶ X} {b : P ⟶ T} {t : T ⟶ Spec (.of K)} (H : IsPullback a b p t)
    (σ : T ⟶ P) (hσ : σ ≫ b = 𝟙 _) (f : P ⟶ Y)
    (s : T) (y : Y) (hy : ∀ z : P, b z = s → f z = y) :
    ∃ V : T.Opens, s ∈ V ∧ (b ⁻¹ᵁ V).ι ≫ f = (b ⁻¹ᵁ V).ι ≫ (b ≫ σ ≫ f) := by
  have : UniversallyClosed b :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @UniversallyClosed) H inferInstance
  exact Global.FunctionsLocalRigidity.globalFunctions_localRigidity b
    (properField_baseChange_restriction_globalFunctions_isIso p x hx H) σ hσ f s y hy

theorem properField_baseChange_globalRigidity
    (p : X ⟶ Spec (.of K)) [UniversallyClosed p] [IsSeparated p]
    [IsReduced X] [ConnectedSpace X] (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)
    {a : P ⟶ X} {b : P ⟶ T} {t : T ⟶ Spec (.of K)} (H : IsPullback a b p t)
    (hopen : IsOpenMap b) [PreconnectedSpace T]
    (σ : T ⟶ P) (hσ : σ ≫ b = 𝟙 _) (f : P ⟶ Y) [Y.IsSeparated]
    (s : T) (y : Y) (hy : ∀ z : P, b z = s → f z = y) : f = b ≫ σ ≫ f := by
  have : UniversallyClosed b :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @UniversallyClosed) H inferInstance
  exact Global.FunctionsRigidity.globalFunctions_globalRigidity b
    (properField_baseChange_restriction_globalFunctions_isIso p x hx H) hopen σ hσ f s y hy

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FieldBaseChangeRigidity
