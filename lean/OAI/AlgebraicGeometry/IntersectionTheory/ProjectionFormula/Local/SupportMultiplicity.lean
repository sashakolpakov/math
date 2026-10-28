import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.DivisorPrime
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.LocalEquation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.SupportCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.OrderPositive
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.EquationRestriction

/-! # Support Multiplicity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SupportMultiplicity

noncomputable section

/-! The coefficients of the actual divisor--support intersection cycle
are precisely the height-one orders of its local equation in the support
stalk. Every component with a positive order occurs in that finite cycle. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CanonicalSurfaceReciprocity

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
  (D : X.DimensionCycleSupport 1) (W : X.DimensionCycleSupport k) (hDW : ¬ W.val ≤ D.val) (x : X.carrier)
  (hxD : x ∈ (D.val : Set X.carrier)) (hxW : x ∈ (W.val : Set X.carrier))
  (r : X.carrier.presheaf.stalk x) (hr : r ≠ 0)
  (he : RingHom.ker (Principal.supportStalkMap X.carrier D.val x hxD).hom = Ideal.span {r})

include hDW he

omit [IsIntegral X.carrier] in
theorem restricted_nonzero : Principal.supportStalkMap X.carrier W.val x hxW r ≠ 0 := by
  exact Support.EquationRestriction.nonzero X.carrier W.val D.val x hxW hxD r he hDW

include m hr

theorem multiplicity_eq_weight
    (p : PrimeSpectrum ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)))
    (hp : p.asIdeal.height = 1) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val W.val (Support.LocalDivisor.support X k W x hxW p) =
      CanonicalSurfaceReciprocity.weight ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)) p
        (Principal.supportStalkMap X.carrier W.val x hxW r) := by
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW
  let f := Principal.supportStalkMap X.carrier W.val x hxW r
  let A : X.DimensionCycleSupport (1 + k) := ⟨Support.LocalDivisor.support X k W x hxW p,
    by rw [Support.LocalDivisor.codimension X k W x hxW p m hp]; omega⟩
  have hxA : x ∈ (A.val : Set X.carrier) := Support.LocalDivisor.point_mem X k W x hxW p
  have hAW : CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ (W.val : Set X.carrier) :=
    Support.LocalDivisor.subset X k W x hxW p
      (A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem
  have hyA : CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) hAW = Y.fromSpecStalk y p := by
    apply (CycleClass.Geometric.GenericPoint.reducedSupportι W.val).isEmbedding.injective
    rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]
    exact Support.LocalDivisor.support_point X k W x hxW p
  have hi := General.LocalEquation.order_eq X m k D W hDW x hxD hxW r hr he A hxA hAW
  rw [hyA] at hi
  have hf : f ≠ 0 := restricted_nonzero X k D W hDW x hxD hxW r he
  have hw := Stalk.DivisorRestriction.order_of_local_element Y y f hf p hp
  have hwQ : (Y.ord (algebraMap (Y.presheaf.stalk y) Y.functionField f) (Y.fromSpecStalk y p) : ℚ) =
      CanonicalSurfaceReciprocity.weight (Y.presheaf.stalk y) p f := by
    simpa only [CanonicalSurfaceReciprocity.weight, Int.cast_natCast] using congrArg (fun n : ℤ => (n : ℚ)) hw
  exact hi.symm.trans hwQ

theorem mem_cycle
    (p : PrimeSpectrum ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)))
    (hp : p.asIdeal.height = 1) (hfp : Principal.supportStalkMap X.carrier W.val x hxW r ∈ p.asIdeal) :
    (⟨Support.LocalDivisor.support X k W x hxW p, by rw [Support.LocalDivisor.codimension X k W x hxW p m hp]; omega⟩ :
      X.DimensionCycleSupport (1 + k)) ∈ (Divisor.SupportCycle.cycle X m k D W).support := by
  let A : X.DimensionCycleSupport (1 + k) := ⟨Support.LocalDivisor.support X k W x hxW p,
    by rw [Support.LocalDivisor.codimension X k W x hxW p m hp]; omega⟩
  have heq := (Divisor.SupportCycle.coefficient X m k D W hDW A).trans
    (multiplicity_eq_weight X m k D W hDW x hxD hxW r hr he p hp)
  have hpos := Principal.OrderPositive.weight_pos _ p hp _
    (restricted_nonzero X k D W hDW x hxD hxW r he) hfp
  exact Finsupp.mem_support_iff.mpr (fun hz => (ne_of_gt hpos) (heq.symm.trans hz))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SupportMultiplicity
