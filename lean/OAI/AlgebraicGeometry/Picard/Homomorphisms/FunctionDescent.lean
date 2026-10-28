import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Function Descent -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FunctionDescent

noncomputable section

/-! Faithfully flat descent of actual global regular functions, obtained
from the affine line and the native effective-epimorphism theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

abbrev functionTarget : Scheme.{u} :=
  Spec (.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))

def globalFunctionEquiv (X : Scheme.{u}) : (X ⟶ functionTarget) ≃ Γ(X, ⊤) :=
  (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).trans (Equiv.funUnique PUnit _)

theorem globalFunctionEquiv_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ functionTarget) :
    globalFunctionEquiv X (f ≫ g) = f.appTop (globalFunctionEquiv Y g) := rfl

theorem appTop_injective_of_epi {X Y : Scheme.{u}} (f : X ⟶ Y) [Epi f] :
    Function.Injective f.appTop := by
  intro r s hrs
  let a := (globalFunctionEquiv Y).symm r
  let b := (globalFunctionEquiv Y).symm s
  have hab : f ≫ a = f ≫ b := by
    apply (globalFunctionEquiv X).injective
    rw [globalFunctionEquiv_comp, globalFunctionEquiv_comp]
    simpa only [a, b, Equiv.apply_symm_apply] using hrs
  have he : a = b := (cancel_epi f).mp hab
  simpa only [a, b, Equiv.apply_symm_apply] using (congrArg (globalFunctionEquiv Y) he)

theorem existsUnique_function_descent {X Y : Scheme.{u}} (f : X ⟶ Y) [EffectiveEpi f]
    (r : Γ(X, ⊤))
    (hr : ∀ {T : Scheme.{u}} (x y : T ⟶ X), x ≫ f = y ≫ f → x.appTop r = y.appTop r) :
    ∃! s : Γ(Y, ⊤), f.appTop s = r := by
  let h := (globalFunctionEquiv X).symm r
  have hrel : ∀ {T : Scheme.{u}} (x y : T ⟶ X), x ≫ f = y ≫ f → x ≫ h = y ≫ h := by
    intro T x y hxy
    apply (globalFunctionEquiv T).injective
    rw [globalFunctionEquiv_comp, globalFunctionEquiv_comp]
    simpa only [h, Equiv.apply_symm_apply] using hr x y hxy
  let d := EffectiveEpi.desc f h hrel
  have hd : f ≫ d = h := EffectiveEpi.fac f h hrel
  refine ⟨globalFunctionEquiv Y d, ?_, ?_⟩
  · exact (globalFunctionEquiv_comp f d).symm.trans
      ((congrArg (globalFunctionEquiv X) hd).trans ((globalFunctionEquiv X).apply_symm_apply r))
  · intro s hs
    apply appTop_injective_of_epi f
    exact hs.trans ((globalFunctionEquiv_comp f d).symm.trans
      ((congrArg (globalFunctionEquiv X) hd).trans ((globalFunctionEquiv X).apply_symm_apply r))).symm

theorem existsUnique_function_descent_of_fpqc {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [QuasiCompact f] (r : Γ(X, ⊤))
    (hr : ∀ {T : Scheme.{u}} (x y : T ⟶ X), x ≫ f = y ≫ f → x.appTop r = y.appTop r) :
    ∃! s : Γ(Y, ⊤), f.appTop s = r := existsUnique_function_descent f r hr

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FunctionDescent
