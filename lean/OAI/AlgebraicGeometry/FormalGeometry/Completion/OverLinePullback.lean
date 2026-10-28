import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.IsoPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentReindexing

/-! # Over Line Pullback -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.OverLinePullback

noncomputable section

/-! Compare actual module-pullback isomorphisms with the ordinary
descent pseudofunctor over a fixed scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Construction

universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

theorem overLineIsoPullbackTo_hom {S : Scheme.{u}} {X Y Z : Over S}
    (f₁ f₂ : Y ⟶ X) (j : Z ⟶ Y) (f₁' f₂' : Z ⟶ X)
    (hj₁ : j ≫ f₁ = f₁') (hj₂ : j ≫ f₂ = f₂') (M : X.left.Modules)
    (e : (Scheme.Modules.pullback f₁.left).obj M ≅ (Scheme.Modules.pullback f₂.left).obj M) :
    (Rigidified.IsoPullback.Construction.lineIsoPullbackTo f₁.left f₂.left j.left f₁'.left f₂'.left
      (congrArg Over.Hom.left hj₁) (congrArg Over.Hom.left hj₂) M e).hom =
      pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S) e.hom j f₁' f₂' hj₁ hj₂ := by
  rw [Picard.PoincareBundle.DescentReindexing.pullHom_reindex (Over.forget S) Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks,
    Picard.PoincareBundle.Geometric.PullHom.pullHom_eq]
  rfl

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.OverLinePullback
