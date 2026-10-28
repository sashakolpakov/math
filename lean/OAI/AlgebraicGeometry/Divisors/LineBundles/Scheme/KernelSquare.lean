import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealModule

/-! # Kernel Square -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.KernelSquare.BundleCycles

noncomputable section

/-! Pullback of regular functions sends the actual kernel ideal
into the kernel ideal in a commuting square of schemes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem schemeAppLE_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

variable {X Z X' Z' : Scheme.{0}} (i : Z ⟶ X) (j : Z' ⟶ X')
    (f : X' ⟶ X) (g : Z' ⟶ Z) (h : g ≫ i = j ≫ f)

include g h in
theorem schemeKernelSquare_mem (U : X.Opens) (a : Γ(X, U)) (ha : a ∈ RingHom.ker (i.app U).hom) :
    f.app U a ∈ RingHom.ker (j.app (f ⁻¹ᵁ U)).hom := by
  let V := j ⁻¹ᵁ (f ⁻¹ᵁ U)
  have hV : V ≤ g ⁻¹ᵁ (i ⁻¹ᵁ U) := by
    change V ≤ (g ≫ i) ⁻¹ᵁ U
    rw [h]
    exact le_rfl
  have H : i.app U ≫ g.appLE (i ⁻¹ᵁ U) V hV =
      f.app U ≫ j.appLE (f ⁻¹ᵁ U) (j ⁻¹ᵁ (f ⁻¹ᵁ U)) le_rfl :=
    (Scheme.Hom.comp_appLE g i U V hV).symm.trans
      ((schemeAppLE_congr h U V hV le_rfl).trans (Scheme.Hom.comp_appLE j f U V le_rfl))
  rw [Scheme.Hom.appLE_eq_app] at H
  have Ha := ConcreteCategory.congr_hom H a
  change g.appLE (i ⁻¹ᵁ U) V hV (i.app U a) = j.app (f ⁻¹ᵁ U) (f.app U a) at Ha
  change i.app U a = 0 at ha
  change j.app (f ⁻¹ᵁ U) (f.app U a) = 0
  exact Ha.symm.trans (by rw [ha, map_zero])

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.KernelSquare.BundleCycles
