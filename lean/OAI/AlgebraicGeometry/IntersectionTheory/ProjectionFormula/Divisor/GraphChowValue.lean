import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorPullback
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ChowMap
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleDegreeTransport

/-! # Graph Chow Value -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.GraphChowValue

noncomputable section

/-! The exact divisor graph pullback evaluated with the divisor as the
first intersection factor, without integrality assumptions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (f : X.toOver ⟶ Y.toOver) (m n : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

local instance : SmoothOfRelativeDimension (m + n) P.space.structureMap :=
  ProductDimension.relativeDimension P m n

theorem value (a : Y.RationalDimensionCycle 1) :
    General.DivisorPullback.pull P f m n (ProperCycleLinearity.cycleToChowQ Y 1 a) =
      ChowPushforwardMap.map P.fst (m + n) m (1 + n) 1 (by omega)
        (ChowMap.map P.space (m + n) n
          (ProperCycleLinearity.cycleToChowQ P.space 1 (P.secondPullbackCycle 1 a))
          (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n))) := by
  obtain ⟨c, hc⟩ := ProperCycleLinearity.cycleToChowQ_surjective P.space (1 + n)
    (ChowMap.map P.space (m + n) n
      (ProperCycleLinearity.cycleToChowQ P.space 1 (P.secondPullbackCycle 1 a))
      (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n)))
  have hi : CycleClass.Thom.IntersectionGeometry.RepresentsIntersection P.space 1 n (P.secondPullbackCycle 1 a) (P.graphCycle f n) c := by
    apply (ProperCycleLinearity.chowIntersection_mk_iff P.space 1 n _ _ c).mp
    rw [ChowMap.graph P.space (m + n) n, Set.mem_singleton_iff]
    exact hc
  have hr : P.RepresentsPullback f n 1 a (ProperCycleLinearity.cyclePushforward P.fst (1 + n) 1 c) := by
    refine ⟨DegreeCast.cycle P.space (Nat.add_comm 1 n) c,
      (ChowSymmetry.Graded.represents_comm P.space 1 n _ _ _).mp hi, ?_⟩
    rw [CycleDegreeTransport.pushforward]
    exact CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X 1 _
  have hp := ((General.DivisorPullbackOnCycles.representsPullback_iff P f m n a _).mp hr).symm
  change General.DivisorPullback.pull P f m n (ProperCycleLinearity.cycleToChowQ Y 1 a) = _ at hp
  rw [← hc, ChowPushforwardMap.map_mk]
  exact hp

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.GraphChowValue
