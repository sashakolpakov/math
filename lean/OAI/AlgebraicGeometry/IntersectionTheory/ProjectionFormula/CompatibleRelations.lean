import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

/-! # Compatible Relations -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompatibleRelations

noncomputable section

/-! Rational relations that also preserve intersection with each
specified fixed support form a submodule. Finite generator lifting
therefore preserves all those intersection classes simultaneously. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

def submodule (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] {ι : Type} (B : ι → X.DimensionCycleSupport q) :
    Submodule ℚ (X.RationalDimensionCycle p) :=
  CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p ⊓ ⨅ i, (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (p + q)).comap
    ((Supports.ProperCycle.intersectionBilinear X m p q).flip (Finsupp.single (B i) 1))

theorem mem_iff (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] {ι : Type} (B : ι → X.DimensionCycleSupport q)
    (a b : X.RationalDimensionCycle p) :
    a - b ∈ submodule X m p q B ↔ CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a b ∧
      ∀ i, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (p + q)
        (Supports.ProperCycle.intersectionBilinear X m p q a (Finsupp.single (B i) 1))
        (Supports.ProperCycle.intersectionBilinear X m p q b (Finsupp.single (B i) 1)) := by
  simp only [submodule, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, map_sub]
  rfl

theorem lift_cycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (R G : Submodule ℚ (X.RationalDimensionCycle p)) (a : X.RationalDimensionCycle p)
    (h : ∀ W ∈ a.support, ∃ b : X.RationalDimensionCycle p, Finsupp.single W 1 - b ∈ R ∧ b ∈ G) :
    ∃ b : X.RationalDimensionCycle p, a - b ∈ R ∧ b ∈ G := by
  choose b hb hg using fun W : a.support => h W.val W.property
  let c := ∑ W : a.support, a W.val • b W
  refine ⟨c, ?_, Submodule.sum_mem G (fun W _ => Submodule.smul_mem G _ (hg W))⟩
  have hs : (∑ W : a.support, a W.val • Finsupp.single W.val (1 : ℚ)) = a := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact (Finset.sum_coe_sort a.support (fun W => Finsupp.single W (a W))).trans a.sum_single
  have hr : (∑ W : a.support, a W.val • (Finsupp.single W.val (1 : ℚ) - b W)) ∈ R :=
    Submodule.sum_mem R (fun W _ => Submodule.smul_mem R _ (hb W))
  simpa only [smul_sub, Finset.sum_sub_distrib, hs] using hr

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompatibleRelations
