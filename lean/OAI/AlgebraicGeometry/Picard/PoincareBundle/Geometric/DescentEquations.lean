import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom

/-! # Descent Equations -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations

noncomputable section

/-!
# Ordinary scheme descent data satisfy native geometric pullback equations
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u v

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom

/-- Pullback of a geometric gluing morphism, using actual scheme pullback composition maps. -/
def nativePullback {X₁ X₂ Y Y' : Scheme.{u}} {L₁ : X₁.Modules} {L₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a : (Scheme.Modules.pullback f₁).obj L₁ ⟶ (Scheme.Modules.pullback f₂).obj L₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    (Scheme.Modules.pullback gf₁).obj L₁ ⟶ (Scheme.Modules.pullback gf₂).obj L₂ :=
  (Scheme.Modules.pullbackComp g f₁ ≪≫ Scheme.Modules.pullbackCongr h₁).inv.app L₁ ≫
    (Scheme.Modules.pullback g).map a ≫
      (Scheme.Modules.pullbackComp g f₂ ≪≫ Scheme.Modules.pullbackCongr h₂).hom.app L₂

variable {ι : Type v} {B : Scheme.{u}} {A : ι → Scheme.{u}} {f : ∀ i, A i ⟶ B}
  (D : KernelLinearization.modulePullbacks.DescentData f)

/-- The ordinary descent data give exactly the native sheaf pullback equation. -/
theorem hom_pullback {Y Y' : Scheme.{u}} (p : Y' ⟶ Y) (q : Y ⟶ B) (q' : Y' ⟶ B)
    (hq : p ≫ q = q') {i j : ι} (x : Y ⟶ A i) (y : Y ⟶ A j)
    (hx : x ≫ f i = q) (hy : y ≫ f j = q)
    (x' : Y' ⟶ A i) (y' : Y' ⟶ A j) (hpx : p ≫ x = x') (hpy : p ≫ y = y') :
    nativePullback (D.hom q x y hx hy) p x' y' hpx hpy =
      D.hom q' x' y' (by rw [← hpx, Category.assoc, hx, hq])
        (by rw [← hpy, Category.assoc, hy, hq]) := by
  unfold nativePullback
  exact (PullHom.pullHom_eq (L₁ := D.obj i) (L₂ := D.obj j)
    (D.hom q x y hx hy) p x' y' hpx hpy).symm.trans
    (D.pullHom_hom p q q' hq x y hx hy x' y' hpx hpy)

/-- Equal choices of the composite coordinate maps induce the usual endpoint transports. -/
theorem nativePullback_congr {X₁ X₂ Y Y' : Scheme.{u}} {L₁ : X₁.Modules} {L₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (a : (Scheme.Modules.pullback f₁).obj L₁ ⟶ (Scheme.Modules.pullback f₂).obj L₂)
    (g : Y' ⟶ Y) {gf₁ gf₁' : Y' ⟶ X₁} {gf₂ gf₂' : Y' ⟶ X₂}
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) (e₁ : gf₁ = gf₁') (e₂ : gf₂ = gf₂') :
    nativePullback a g gf₁' gf₂' (h₁.trans e₁) (h₂.trans e₂) =
      eqToHom (congrArg (fun r => (Scheme.Modules.pullback r).obj L₁) e₁.symm) ≫
        nativePullback a g gf₁ gf₂ h₁ h₂ ≫
          eqToHom (congrArg (fun r => (Scheme.Modules.pullback r).obj L₂) e₂) := by
  subst gf₁'
  subst gf₂'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations
