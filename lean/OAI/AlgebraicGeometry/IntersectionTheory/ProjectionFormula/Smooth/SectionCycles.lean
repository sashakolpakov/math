import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SectionPair
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleLinearExpansion
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.CycleSupport

/-! # Section Cycles -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SectionCycles

noncomputable section

/-! The section intersection identity extends bilinearly to all
properly meeting rational cycles while retaining their original supports. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.EmbeddingCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.EmbeddingCycle.Maps

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (s : Y.toOver ⟶ X.toOver) [IsClosedImmersion s.left]
  (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
  [GeometricallyIntegral (show X.carrier ⟶ Y.carrier from f.left)] (hs : s ≫ f = 𝟙 Y.toOver)
  (m n r : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
  (hd : n + r = m) (p q : ℕ) (b : Y.RationalDimensionCycle p) (d : Y.RationalDimensionCycle q)
  (hbd : CycleClass.Thom.IntersectionGeometry.MeetProperly Y p q b d)

omit [IsClosedImmersion s.left] in
theorem flatMap_eq_mapDomain : Cycle.flatMap f p b =
    Finsupp.mapDomain (Integral.FiberCycles.support f m n p) b := by
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, Finsupp.mapDomain_add, ha, hb]
  | single B c =>
    rw [Cycle.flatMap, Finsupp.linearCombination_single,
      Integral.FiberCycles.cycle_single f m n p B, Finsupp.smul_single,
      smul_eq_mul, mul_one, Finsupp.mapDomain_single]

include hs hd hbd in
theorem meets : CycleClass.Thom.IntersectionGeometry.MeetProperly X p (q + r) (Cycle.flatMap f p b)
    (ProperCycleLinearity.cyclePushforward s q (q + r) d) := by
  rw [flatMap_eq_mapDomain f m n p b, ← Closed.EmbeddingCycle.Maps.embed_eq_pushforward s n m q (q + r) (by omega)]
  intro A hA E hE
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hA)
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hE)
  exact SectionPair.proper s f hs m n r hd p q B D (hbd B hB D hD)

include hs hd hbd in
theorem cycle : Supports.ProperCycle.intersectionBilinear X m p (q + r) (Cycle.flatMap f p b)
    (ProperCycleLinearity.cyclePushforward s q (q + r) d) =
    ProperCycleLinearity.cyclePushforward s (p + q) (p + (q + r)) (Supports.ProperCycle.intersectionBilinear Y n p q b d) := by
  rw [← Closed.EmbeddingCycle.Maps.embed_eq_pushforward s n m q (q + r) (by omega),
    ← Closed.EmbeddingCycle.Maps.embed_eq_pushforward s n m (p + q) (p + (q + r)) (by omega)]
  let F := (Supports.ProperCycle.intersectionBilinear X m p (q + r)).compl₁₂ (Cycle.flatMap f p)
    (Closed.EmbeddingCycle.Maps.embed s n m q (q + r) (by omega))
  change F b d = _
  rw [CycleLinearExpansion.bilinear_sum F b d, CycleLinearExpansion.intersection Y n p q b d]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro B hB
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  change Supports.ProperCycle.intersectionBilinear X m p (q + r) (Cycle.flatMap f p (Finsupp.single B 1))
    (Closed.EmbeddingCycle.Maps.embed s n m q (q + r) (by omega) (Finsupp.single D 1)) = _
  rw [Cycle.flatMap, Finsupp.linearCombination_single,
    Integral.FiberCycles.cycle_single f m n p B, one_smul, Closed.EmbeddingCycle.Maps.embed_single]
  simp only [Supports.ProperCycle.intersectionBilinear, Finsupp.linearCombination_single, one_smul]
  exact SectionPair.pair s f hs m n r hd p q B D (hbd B hB D hD)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SectionCycles
