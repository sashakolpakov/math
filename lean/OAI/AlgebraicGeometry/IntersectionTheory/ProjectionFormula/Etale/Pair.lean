import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.FiberCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.SupportMultiplicity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.FiberCycles

/-! # Pair -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.Pair

noncomputable section

/-! The native projection identity for a properly positioned pair
whose support fibers over the target intersection are etale. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
  [GeometricallyIntegral (show X.carrier ⟶ Y.carrier from f.left)]
  (m n p q s : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
  (hd : q + n = s + m) (A : Y.DimensionCycleSupport p) (W : X.DimensionCycleSupport q)
  (B : Y.DimensionCycleSupport s) (hB : ProperCycleLinearity.imageSupport f W.val = B.val)
  (hX : Supports.ProperCycle.pairMeetsProperly X p q (Integral.FiberCycles.support f m n p A) W)
  (hY : Supports.ProperCycle.pairMeetsProperly Y p s A B) (U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).Opens)
  [Etale (U.ι ≫ Support.Map.supportImageMap f W.val)]
  (hgood : ∀ D : Y.DimensionCycleSupport (p + s),
    CycleClass.Thom.IntersectionGeometry.supportPoint D.val ∈ (A.val : Set Y.carrier) →
    ∀ hDW : CycleClass.Thom.IntersectionGeometry.supportPoint D.val ∈ (ProperCycleLinearity.imageSupport f W.val : Set Y.carrier),
      CycleClass.Thom.IntersectionGeometry.supportPreimage (ProperCycleLinearity.imageSupport f W.val) (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) hDW ∈
        Proper.EtaleRestriction.good (Support.Map.supportImageMap f W.val) U)

local instance : IsLocallyNoetherian Y.toOver.left := inferInstanceAs (IsLocallyNoetherian Y.carrier)

omit [Smooth f.left] [GeometricallyIntegral (show X.carrier ⟶ Y.carrier from f.left)]
  [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
  [Etale (U.ι ≫ Support.Map.supportImageMap f W.val)] in
theorem image_point (C : X.DimensionCycleSupport (p + q)) (D : Y.DimensionCycleSupport (p + s))
    (h : ProperCycleLinearity.imageSupport f C.val = D.val) : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) = CycleClass.Thom.IntersectionGeometry.supportPoint D.val := by
  exact (irreducibleSetEquivPoints.apply_symm_apply _).symm.trans (congrArg CycleClass.Thom.IntersectionGeometry.supportPoint h)

include hB hX in
theorem outside (D : Y.DimensionCycleSupport (p + s))
    (hD : CycleClass.Thom.IntersectionGeometry.supportPoint D.val ∉ (A.val : Set Y.carrier) ∩ B.val) :
    ProperCycleLinearity.cyclePushforward f (p + q) (p + s)
      (Supports.ProperCycle.pairCycle X m p q (Integral.FiberCycles.support f m n p A) W) D = 0 := by
  have he := PushforwardCoefficientCongruence.eq f (p + q) (p + s)
    (Supports.ProperCycle.pairCycle X m p q (Integral.FiberCycles.support f m n p A) W) 0 D
  rw [he]
  · simp
  · intro C hC
    rw [Supports.ProperCycle.pairCycle_apply X m p q _ W hX, Finsupp.zero_apply]
    apply dite_eq_right
    intro hx
    have hxy := image_point f p q s C D hC
    have hxA : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) ∈ (A.val : Set Y.carrier) := by
      have hh := hx.1
      change CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈
        (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport (show X.carrier ⟶ Y.carrier from f.left) A.val : Set X.carrier) at hh
      rwa [Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport_coe] at hh
    have hxB : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) ∈ (B.val : Set Y.carrier) := by
      rw [← hB, ProperCycleLinearity.imageSupport_eq_image]
      exact ⟨CycleClass.Thom.IntersectionGeometry.supportPoint C.val, hx.2, rfl⟩
    exact hD (hxy ▸ ⟨hxA, hxB⟩)

include hd hB hX hY hgood in
theorem pair : ProperCycleLinearity.cyclePushforward f (p + q) (p + s)
    (Supports.ProperCycle.pairCycle X m p q (Integral.FiberCycles.support f m n p A) W) =
      (f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint W.val) : ℚ) • Supports.ProperCycle.pairCycle Y n p s A B := by
  ext D
  rw [Finsupp.smul_apply, Supports.ProperCycle.pairCycle_apply Y n p s A B hY]
  by_cases hD : CycleClass.Thom.IntersectionGeometry.supportPoint D.val ∈ (A.val : Set Y.carrier) ∩ B.val
  · have hDW : CycleClass.Thom.IntersectionGeometry.supportPoint D.val ∈ (ProperCycleLinearity.imageSupport f W.val : Set Y.carrier) := hB.symm ▸ hD.2
    let y := CycleClass.Thom.IntersectionGeometry.supportPreimage (ProperCycleLinearity.imageSupport f W.val) (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) hDW
    have hy := hgood D hD.1 hDW
    have hc : ∀ C : X.DimensionCycleSupport (p + q), ProperCycleLinearity.imageSupport f C.val = D.val →
        Supports.ProperCycle.pairCycle X m p q (Integral.FiberCycles.support f m n p A) W C =
          if CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W.val : Set X.carrier) then CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity Y A.val B.val D.val else 0 := by
      intro C hC
      rw [Supports.ProperCycle.pairCycle_apply X m p q _ W hX]
      by_cases hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W.val : Set X.carrier)
      · rw [ite_eq_left hxW]
        have hxy := image_point f p q s C D hC
        have hxU : CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW ∈ U := by
          apply Proper.EtaleRestriction.preimage_le (Support.Map.supportImageMap f W.val) U
          change Support.Map.supportImageMap f W.val (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW) ∈
            Proper.EtaleRestriction.good (Support.Map.supportImageMap f W.val) U
          have he : Support.Map.supportImageMap f W.val (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW) = y := by
            apply (CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W.val)).isClosedEmbedding.injective
            have hh := congrArg (fun g : CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val ⟶ Y.carrier =>
              g (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW)) (Support.Map.supportImageMap_inclusion f W.val)
            exact hh.trans ((congrArg f.left (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W.val _ hxW)).trans
              (hxy.trans (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec (ProperCycleLinearity.imageSupport f W.val) _ hDW).symm))
          rw [he]
          exact hy
        change CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X
          (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport (show X.carrier ⟶ Y.carrier from f.left) A.val) W.val C.val = _
        rw [← hB]
        exact SupportMultiplicity.multiplicity f m n W.val C.val (ProperCycleLinearity.imageSupport f W.val)
          A.val D.val (Support.Map.supportImageMap f W.val) (Support.Map.supportImageMap_inclusion f W.val).symm
          U hxW hDW hD.1 hxy hxU
      · rw [ite_eq_right hxW]
        exact dite_eq_right (fun h => hxW h.2)
    have he := Support.FiberCycle.coefficient f m n (p + q) (p + s) (by omega) W.val U y hy D
      (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec (ProperCycleLinearity.imageSupport f W.val) _ hDW)
      (Supports.ProperCycle.pairCycle X m p q (Integral.FiberCycles.support f m n p A) W)
      (CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity Y A.val B.val D.val) hc
    exact he.trans (mul_comm _ _)
  · rw [outside f m n p q s A W B hB hX D hD]
    rw [show CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity Y A.val B.val D.val = 0 from dite_eq_right hD, smul_zero]

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.Pair
