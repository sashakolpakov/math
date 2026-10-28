import OAI.AlgebraicGeometry.Comparison.Betti.ProductHigherDolbeault
import OAI.AlgebraicGeometry.Comparison.Betti.CoordinateOneFormElimination
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts
import OAI.Analysis.DifferentialForms.Manifold.OpenEquivalence

/-! # Product Anti Dolbeault Primitive -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProductAntiDolbeaultPrimitive

noncomputable section

/-! Global primitives for the actual antiholomorphic sheaf differential
on products of ordinary and punctured complex lines. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultCharts

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_product_antiForm_primitive (ε : ι → Bool) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) (n + 1))
    (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) a = 0) (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree 0 (n + 1) a) :
    ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) n,
      DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree 0 n t ∧ DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n t = a := by
  cases n with
  | zero =>
    obtain ⟨t, ht⟩ := CoordinateOneFormElimination.Dolbeault.exists_product_oneForm_dolbeault_primitive ε a ha hpure
    exact ⟨t, fun x => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero (ι → ℂ) (t x), ht⟩
  | succ n =>
    exact ProductHigherDolbeault.exists_product_higherForm_dolbeault_primitive ε n 0 (n + 1) (by omega) a ha hpure

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem antiDolbeault_primitive_on_chart
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (W : Opens E) (hW : W ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e) (n : ℕ)
    (hcoord : ∀ a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm W (n + 1), DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) a = 0 →
      DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree 0 (n + 1) a →
      ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm W n, DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree 0 n t ∧ DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n t = a)
    (a : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e W) (n + 1))
    (ha : DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e W) (n + 1) a = 0) :
    ∃ t : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e W) n,
      DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e W) n t = a := by
  let A := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn e he W hW a.val
  have hAp : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree 0 (n + 1) A :=
    DivisorClass.Chern.Open.ManifoldBidegree.openManifoldHasBidegree_toChartOn e he W hW a.property
  have hA : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) A = 0 := by
    rw [← DivisorClass.Chern.Manifold.DolbeaultCharts.openManifoldDolbeaultD_toChartOn e he W hW (by omega) a.property]
    have hz : DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD 0 (n + 1) (n + 1) a.val = 0 := congrArg Subtype.val ha
    rw [hz, map_zero]
  obtain ⟨t, htp, ht⟩ := hcoord A hA hAp
  let T := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.fromChartOn e he W t
  have hT : DivisorClass.Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree 0 n T :=
    DivisorClass.Chern.Open.ManifoldBidegree.openManifoldHasBidegree_fromChartOn e he W hW (by omega) htp
  refine ⟨⟨T, hT⟩, Subtype.ext ?_⟩
  apply (Analysis.DifferentialForms.Manifold.ChartEquiv.manifoldChartOpenFormEquiv e he W hW (n + 1)).injective
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn e he W hW (DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD 0 n n T) = A
  rw [DivisorClass.Chern.Manifold.DolbeaultCharts.openManifoldDolbeaultD_toChartOn e he W hW (by omega) hT,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toChartOn_fromChartOn, ht]

theorem openDomain_antiDolbeault_primitive (U : Opens E) (x₀ : U) (n : ℕ)
    (hcoord : ∀ a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1), DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) a = 0 →
      DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree 0 (n + 1) a →
      ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n, DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree 0 n t ∧ DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n t = a) :
    ∀ a : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens U) (n + 1),
      DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (⊤ : Opens U) (n + 1) a = 0 →
      ∃ t : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens U) n,
        DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (⊤ : Opens U) n t = a := by
  let e := chartAt E x₀
  have hU : U ≤ Analysis.DifferentialForms.Manifold.ChartEquiv.chartTargetOpen e := by
    intro y hy
    change y ∈ (chartAt E x₀).target
    rwa [Analysis.DifferentialForms.Manifold.OpenEquivalence.open_chartAt_target]
  have hpre : Analysis.DifferentialForms.Manifold.ChartEquiv.chartPreimageOpen e U = (⊤ : Opens U) := by
    ext x
    change (x ∈ (chartAt E x₀).source ∧ (chartAt E x₀) x ∈ U) ↔ True
    rw [Analysis.DifferentialForms.Manifold.OpenEquivalence.open_chartAt_source, Analysis.DifferentialForms.Manifold.OpenEquivalence.open_chartAt_apply]
    exact iff_true_intro ⟨Set.mem_univ x, x.property⟩
  have h := antiDolbeault_primitive_on_chart e (chart_mem_atlas E x₀) U hU n hcoord
  erw [hpre] at h
  exact h

theorem product_antiDolbeault_global_primitive (ε : ι → Bool) (n : ℕ) :
    ∀ a : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm (ι → ℂ) (⊤ : Opens (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε)) (n + 1),
      DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (⊤ : Opens (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε)) (n + 1) a = 0 →
      ∃ t : DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm (ι → ℂ) (⊤ : Opens (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε)) n,
        DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (⊤ : Opens (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε)) n t = a := by
  have hone : (fun _ : ι => (1 : ℂ)) ∈ ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε := by
    simp only [ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct, DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc, Opens.mem_mk, Set.mem_iInter,
      Set.mem_preimage]
    intro i
    cases ε i <;> simp [PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen, PuncturedCauchy.Dolbeault.puncturedComplexOpen]
  exact openDomain_antiDolbeault_primitive (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) ⟨_, hone⟩ n
    (exists_product_antiForm_primitive ε n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProductAntiDolbeaultPrimitive
