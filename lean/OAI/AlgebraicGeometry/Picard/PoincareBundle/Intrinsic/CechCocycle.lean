import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations

/-! # Cech Cocycle -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.CechCocycle

noncomputable section

/-!
# The native geometric Čech cocycle of ordinary scheme descent data
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations

variable {A B : Scheme.{u}} (f : A ⟶ B)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))

/-- Three compatible coordinate pairs pull the overlap gluing to the native geometric cocycle. -/
theorem triple_cocycle {Y Z : Scheme.{u}} (q : Y ⟶ B) (q' : Z ⟶ B)
    (x y : Y ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q)
    (a b c : Z ⟶ A) (ha : a ≫ f = q') (hb : b ≫ f = q') (hc : c ≫ f = q')
    (p₁₂ p₁₃ p₂₃ : Z ⟶ Y)
    (h₁₂₁ : p₁₂ ≫ x = a) (h₁₂₂ : p₁₂ ≫ y = b)
    (h₁₃₁ : p₁₃ ≫ x = a) (h₁₃₂ : p₁₃ ≫ y = c)
    (h₂₃₁ : p₂₃ ≫ x = b) (h₂₃₂ : p₂₃ ≫ y = c) :
    Geometric.DescentEquations.nativePullback (D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy)
          p₁₂ a b h₁₂₁ h₁₂₂ ≫
        Geometric.DescentEquations.nativePullback (D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy)
          p₂₃ b c h₂₃₁ h₂₃₂ =
      Geometric.DescentEquations.nativePullback (D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy)
        p₁₃ a c h₁₃₁ h₁₃₂ := by
  have hq₁₂ : p₁₂ ≫ q = q' := by rw [← hx, ← Category.assoc, h₁₂₁, ha]
  have hq₁₃ : p₁₃ ≫ q = q' := by rw [← hx, ← Category.assoc, h₁₃₁, ha]
  have hq₂₃ : p₂₃ ≫ q = q' := by rw [← hx, ← Category.assoc, h₂₃₁, hb]
  rw [Geometric.DescentEquations.hom_pullback D p₁₂ q q' hq₁₂ x y hx hy a b h₁₂₁ h₁₂₂,
    Geometric.DescentEquations.hom_pullback D p₂₃ q q' hq₂₃ x y hx hy b c h₂₃₁ h₂₃₂,
    Geometric.DescentEquations.hom_pullback D p₁₃ q q' hq₁₃ x y hx hy a c h₁₃₁ h₁₃₂]
  exact D.hom_comp q' (i₁ := PUnit.unit) (i₂ := PUnit.unit) (i₃ := PUnit.unit) a b c ha hb hc

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.CechCocycle
