import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldDolbeaultPoincare
import OAI.AlgebraicGeometry.DivisorClass.Chern.PureManifoldDolbeaultSheaf
import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.SheafLocalExact

/-! # Anti Dolbeault Sheaf Exactness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AntiDolbeaultSheafExactness

noncomputable section

/-! Exactness in every positive degree of the original antiholomorphic
Dolbeault sheaf complex, using the actual local primitives. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem antiManifoldLocalDolbeaultPoincare (U : Opens M) (q : ℕ)
    (a : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E U (q + 1)) (ha : DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD U (q + 1) a = 0) (x : U) :
    ∃ V : Opens M, x.val ∈ V ∧ ∃ hV : V ≤ U, ∃ t : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E V q,
      DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD V q t = DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormRestrict hV a := by
  have hz : DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD 0 (q + 1) (q + 1) a.val = 0 := congrArg Subtype.val ha
  obtain ⟨V, hxV, hV, t, htp, ht⟩ := ManifoldDolbeaultPoincare.manifoldLocalDolbeaultPoincare U q 0 q (by omega) a.val hz a.property x
  exact ⟨V, hxV, hV, ⟨t, htp⟩, Subtype.ext ht⟩

def antiManifoldDolbeaultSequence (q : ℕ) : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M)) :=
  ShortComplex.mk (DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M q) (DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap E M (q + 1))
    (DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafMap_squared E M q)

theorem antiManifoldDolbeaultSequence_exact (q : ℕ) : (antiManifoldDolbeaultSequence E M q).Exact := by
  apply DivisorClass.Chern.Abelian.SheafLocalExact.abelianSheaf_exact_of_local_lifts (TopCat.of M) (antiManifoldDolbeaultSequence E M q)
  intro U a ha x hx
  change DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD U (q + 1) a = 0 at ha
  obtain ⟨V, hxV, hVU, t, ht⟩ := antiManifoldLocalDolbeaultPoincare E M U q a ha ⟨x, hx⟩
  exact ⟨V, hxV, hVU, t, ht⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.AntiDolbeaultSheafExactness
