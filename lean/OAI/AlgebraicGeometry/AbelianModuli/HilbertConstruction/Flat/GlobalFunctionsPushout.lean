import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.GlobalTensorComparison

/-! # Global Functions Pushout -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.GlobalFunctionsPushout

noncomputable section

/-! The global-function square is a pushout after flat affine base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine Y] [CompactSpace X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

theorem flatBaseChange_globalFunctions_isPushout
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) [Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)] :
    IsPushout f.appTop g.appTop a.appTop b.appTop := by
  let B := Affine.TensorSectionComparison.morphismGlobalAlgebra g
  let A := Coefficient.AlgebraPresheaf.coefficientAlgebraSections f.appTop.hom ⊤
  let C := Coefficient.AlgebraPresheaf.coefficientAlgebraSections (a.appTop.hom.comp f.appTop.hom) (a ⁻¹ᵁ ⊤)
  let i : B →ₐ[Γ(S, ⊤)] C :=
    (Coefficient.AlgebraPullback.coefficientAlgebraGlobalRestriction _ B b.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) (a ⁻¹ᵁ ⊤)).hom
  let j : A →ₐ[Γ(S, ⊤)] C := (Coefficient.AlgebraPullback.coefficientAlgebraPullbackApp a f.appTop.hom ⊤).hom
  have h := RingPushoutTensorComparison.isPushout_of_tensorLift_bijective i j (GlobalTensorComparison.flat_globalTensorComparison_bijective H)
  have hA : CommRingCat.ofHom (algebraMap Γ(S, ⊤) A) = f.appTop := by
    change f.appTop ≫ X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens))) = f.appTop
    rw [X.presheaf.map_id, Category.comp_id]
  have hi : CommRingCat.ofHom i.toRingHom = b.appTop := by
    change b.appTop ≫ P.presheaf.map (𝟙 (Opposite.op (⊤ : P.Opens))) = b.appTop
    rw [P.presheaf.map_id, Category.comp_id]
  have hB : CommRingCat.ofHom (algebraMap Γ(S, ⊤) B) = g.appTop := rfl
  have hj : CommRingCat.ofHom j.toRingHom = a.appTop := rfl
  rw [hA, hB, hi, hj] at h
  exact h.flip

theorem flatBaseChange_globalFunctions_isIso
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) [Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)]
    [IsIso f.appTop] : IsIso b.appTop :=
  (flatBaseChange_globalFunctions_isPushout H).isIso_inr_of_isIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.GlobalFunctionsPushout
