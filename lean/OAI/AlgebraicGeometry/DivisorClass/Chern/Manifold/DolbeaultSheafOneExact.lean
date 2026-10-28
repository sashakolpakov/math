import OAI.AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultPoincare
import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.SheafLocalExact

/-! # Dolbeault Sheaf One Exact -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultSheafOneExact

noncomputable section

/-! Actual degree-one Dolbeault sheaf exactness on complex manifolds. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

def pureManifoldDolbeaultOneSequence : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M)) :=
  ShortComplex.mk (PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 0) (PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M 1)
    (PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap_squared E M 0)

variable [FiniteDimensional ℂ E]

theorem pureManifoldDolbeaultOneSequence_exact : (pureManifoldDolbeaultOneSequence E M).Exact := by
  apply Abelian.SheafLocalExact.abelianSheaf_exact_of_local_lifts (TopCat.of M) (pureManifoldDolbeaultOneSequence E M)
  intro U a ha x hx
  change DolbeaultCharts.pureOpenManifoldDolbeaultD U 1 a = 0 at ha
  obtain ⟨V, hxV, hVU, t, ht⟩ := DolbeaultPoincare.manifoldLocalDolbeaultPoincare_one U a ha ⟨x, hx⟩
  exact ⟨V, hxV, hVU, t, ht⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultSheafOneExact
