import Mathlib.AlgebraicGeometry.Scheme

/-! # Section Pullback Composition -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionPullbackComposition

noncomputable section

/-! Explicit value-level identities for pulling regular sections
through composable scheme maps and equal morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y Z : Scheme.{u}}

theorem appLE_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (hg : V ≤ g ⁻¹ᵁ U) (hf : W ≤ f ⁻¹ᵁ V) (hfg : W ≤ (f ≫ g) ⁻¹ᵁ U)
    (s : Γ(Z, U)) :
    f.appLE V W hf (g.appLE U V hg s) = (f ≫ g).appLE U W hfg s :=
  congrArg (fun k : Γ(Z, U) ⟶ Γ(X, W) => k s)
    (Scheme.Hom.appLE_comp_appLE f g U V W hg hf)

theorem appLE_congr_apply {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) (s : Γ(Y, U)) :
    f.appLE U V hf s = g.appLE U V hg s := by
  subst g
  rfl

theorem appLE_comp_preimage_apply (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Z.Opens) (W : X.Opens) (h : W ≤ (f ≫ g) ⁻¹ᵁ U) (s : Γ(Z, U)) :
    (f ≫ g).appLE U W h s = f.appLE (g ⁻¹ᵁ U) W h (g.app U s) :=
  congrArg (fun k : Γ(Z, U) ⟶ Γ(X, W) => k s) (Scheme.Hom.comp_appLE f g U W h)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionPullbackComposition
