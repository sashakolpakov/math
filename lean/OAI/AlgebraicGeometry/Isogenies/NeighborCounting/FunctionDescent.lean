import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Function Descent -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FunctionDescent

noncomputable section

/-! Descent of regular functions via their actual representing affine line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def functionScheme : Scheme.{u} :=
  Spec (.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))

def functionEquiv (X : Scheme.{u}) : (X ⟶ functionScheme) ≃ Γ(X, ⊤) where
  toFun f := AffineSpace.toSpecMvPolyIntEquiv PUnit f PUnit.unit
  invFun r := (AffineSpace.toSpecMvPolyIntEquiv PUnit).symm (fun _ ↦ r)
  left_inv f := by
    apply (AffineSpace.toSpecMvPolyIntEquiv PUnit).injective
    rw [Equiv.apply_symm_apply]
  right_inv r := by
    exact congrFun ((AffineSpace.toSpecMvPolyIntEquiv PUnit).apply_symm_apply (fun _ ↦ r)) PUnit.unit

theorem functionEquiv_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ functionScheme) :
    functionEquiv X (f ≫ g) = f.appTop (functionEquiv Y g) := rfl

theorem functionMap_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, ⊤)) :
    f ≫ (functionEquiv Y).symm r = (functionEquiv X).symm (f.appTop r) := by
  apply (functionEquiv X).injective
  rw [functionEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem appTop_injective_of_epi {X Y : Scheme.{u}} (f : X ⟶ Y) [Epi f] :
    Function.Injective f.appTop := by
  intro r s h
  apply (functionEquiv Y).symm.injective
  apply (cancel_epi f).mp
  rw [functionMap_comp, functionMap_comp, h]

/-- A regular function compatible on every equal-image pair descends
uniquely through an effective epimorphism of actual schemes. -/
theorem existsUnique_function_descent {X Y : Scheme.{u}} (f : X ⟶ Y) [EffectiveEpi f]
    (r : Γ(X, ⊤))
    (hr : ∀ {T : Scheme.{u}} (x y : T ⟶ X), x ≫ f = y ≫ f → x.appTop r = y.appTop r) :
    ∃! s : Γ(Y, ⊤), f.appTop s = r := by
  let a := (functionEquiv X).symm r
  have ha : ∀ {T : Scheme.{u}} (x y : T ⟶ X), x ≫ f = y ≫ f → x ≫ a = y ≫ a := by
    intro T x y hxy
    apply (functionEquiv T).injective
    rw [functionEquiv_comp, functionEquiv_comp]
    have he : functionEquiv X a = r := (functionEquiv X).apply_symm_apply r
    rw [he]
    exact hr x y hxy
  let d := EffectiveEpi.desc f a ha
  refine ⟨functionEquiv Y d, ?_, ?_⟩
  · exact (functionEquiv_comp f d).symm.trans
      ((congrArg (functionEquiv X) (EffectiveEpi.fac f a ha)).trans
        ((functionEquiv X).apply_symm_apply r))
  · intro s hs
    apply appTop_injective_of_epi f
    exact hs.trans ((functionEquiv_comp f d).symm.trans
      ((congrArg (functionEquiv X) (EffectiveEpi.fac f a ha)).trans
        ((functionEquiv X).apply_symm_apply r))).symm

def globalFunctionPresheaf : Scheme.{u}ᵒᵖ ⥤ Type u :=
  Scheme.Γ ⋙ forget CommRingCat

def globalFunctionRepresentation : globalFunctionPresheaf.RepresentableBy functionScheme where
  homEquiv := functionEquiv _
  homEquiv_comp f g := functionEquiv_comp f g

theorem globalFunctions_fpqc_sheaf :
    Presheaf.IsSheaf Scheme.fpqcTopology globalFunctionPresheaf := by
  have : globalFunctionPresheaf.IsRepresentable := globalFunctionRepresentation.isRepresentable
  exact (isSheaf_iff_isSheaf_of_type Scheme.fpqcTopology globalFunctionPresheaf).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fpqcTopology) globalFunctionPresheaf)

theorem globalFunctions_fppf_sheaf :
    Presheaf.IsSheaf Scheme.fppfTopology globalFunctionPresheaf := by
  have : globalFunctionPresheaf.IsRepresentable := globalFunctionRepresentation.isRepresentable
  exact (isSheaf_iff_isSheaf_of_type Scheme.fppfTopology globalFunctionPresheaf).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fppfTopology) globalFunctionPresheaf)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FunctionDescent
