import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PullbackPointMorphism
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentReindexing

/-! # Pullback Point Morphism Over -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PullbackPointMorphismOver

noncomputable section

/-! Pullback-point morphisms in a slice use their literal underlying
scheme-module morphisms, including the native composition comparisons. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem pullbackPointMorphism_over {S : Scheme.{0}} {X X' Z : Over S}
    (v : X' ⟶ X) (L : X.left.Modules) (x y : Z ⟶ X')
    (h : (Scheme.Modules.pullback (x ≫ v).left).obj L ⟶ (Scheme.Modules.pullback (y ≫ v).left).obj L) :
    PullbackPointMorphism.pullbackPointMorphism (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S) v L x y h =
      PullbackPointMorphism.pullbackPointMorphism Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks v.left L x.left y.left h := by
  unfold PullbackPointMorphism.pullbackPointMorphism
  erw [Picard.PoincareBundle.DescentReindexing.mapComp_reindex (Over.forget S)
    Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks x v (x ≫ v) rfl,
    Picard.PoincareBundle.DescentReindexing.mapComp_reindex (Over.forget S)
      Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks y v (y ≫ v) rfl]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PullbackPointMorphismOver
