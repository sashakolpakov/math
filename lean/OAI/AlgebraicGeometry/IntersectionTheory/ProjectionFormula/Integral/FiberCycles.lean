import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.FiberGrading
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Cycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardComposition
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PulledSupport

/-! # Fiber Cycles -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.FiberCycles

noncomputable section

/-! Smooth inverse-image cycles with integral fibers are the native graded
components of extension along actual fiber generic points. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PulledSupport.BundleCycles OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
  [Smooth (show X.carrier ⟶ Y.carrier from f.left)] [GeometricallyIntegral (show X.carrier ⟶ Y.carrier from f.left)]
  (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  [SmoothOfRelativeDimension n Y.structureMap]

local instance : IsLocallyNoetherian X.toOver.left :=
  inferInstanceAs (IsLocallyNoetherian X.carrier)

local instance : IsLocallyNoetherian Y.toOver.left :=
  inferInstanceAs (IsLocallyNoetherian Y.carrier)

include m n

theorem codimension (W : IrreducibleCloseds Y.carrier) :
    X.supportCodimension (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport (show X.carrier ⟶ Y.carrier from f.left) W) = Y.supportCodimension W := by
  have hx := IntermediateSupports.support_coheight X m _
    (⟨Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport (show X.carrier ⟶ Y.carrier from f.left) W, rfl⟩ : X.DimensionCycleSupport _)
  have hy := IntermediateSupports.support_coheight Y n _
    (⟨W, rfl⟩ : Y.DimensionCycleSupport _)
  have hp : CycleClass.Thom.IntersectionGeometry.supportPoint (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport (show X.carrier ⟶ Y.carrier from f.left) W) =
      Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (show X.carrier ⟶ Y.carrier from f.left) (CycleClass.Thom.IntersectionGeometry.supportPoint W) := Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport_genericPoint (show X.carrier ⟶ Y.carrier from f.left) W
  have he : (X.supportCodimension (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport (show X.carrier ⟶ Y.carrier from f.left) W) : ℕ∞) =
      Y.supportCodimension W := hx.symm.trans
    ((congrArg Order.coheight hp).trans ((FiberGrading.coheight (show X.carrier ⟶ Y.carrier from f.left) (CycleClass.Thom.IntersectionGeometry.supportPoint W)).trans hy))
  exact_mod_cast he

def support (p : ℕ) (B : Y.DimensionCycleSupport p) : X.DimensionCycleSupport p :=
  ⟨Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport (show X.carrier ⟶ Y.carrier from f.left) B.val, (codimension f m n B.val).trans B.property⟩

theorem support_point (p : ℕ) (B : Y.DimensionCycleSupport p) :
    CycleClass.Thom.IntersectionGeometry.supportPoint (support f m n p B).val = Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (show X.carrier ⟶ Y.carrier from f.left) (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) :=
  Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport_genericPoint (show X.carrier ⟶ Y.carrier from f.left) B.val

theorem cycle_single (p : ℕ) (B : Y.DimensionCycleSupport p) :
    ProjectionFormula.Smooth.Cycle.cycle f p B = Finsupp.single (support f m n p B) 1 := by
  ext A
  rw [ProjectionFormula.Smooth.Cycle.cycle_apply f p m n, Finsupp.single_apply]
  congr 1
  apply propext
  constructor
  · intro ha
    have hle : A.val ≤ (support f m n p B).val := by
      change (A.val : Set X.carrier) ⊆ (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport (show X.carrier ⟶ Y.carrier from f.left) B.val : Set X.carrier)
      rw [Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport_coe]
      apply (Supports.supportPoint_mem_iff_subset (ProjectionFormula.Smooth.Cycle.support f p B) A.val).mp
      change (show X.carrier ⟶ Y.carrier from f.left) (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) ∈ (B.val : Set Y.carrier)
      have ha' : (show X.carrier ⟶ Y.carrier from f.left) (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) =
          CycleClass.Thom.IntersectionGeometry.supportPoint B.val := ha
      exact ha'.symm ▸ (B.val.isIrreducible.isGenericPoint_genericPoint B.val.isClosed).mem
    apply Eq.symm
    apply Subtype.ext
    by_contra hn
    have hh := Supports.codimension_strictAnti X m (lt_of_le_of_ne hle hn)
    rw [A.property, (support f m n p B).property] at hh
    exact Nat.lt_irrefl p hh
  · rintro rfl
    rw [support_point, Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection]

theorem flatMap_supportInDegree (p : ℕ) (W : IrreducibleCloseds Y.carrier) :
    ProjectionFormula.Smooth.Cycle.flatMap f p (CycleClass.Thom.IntersectionGeometry.supportInDegree Y p W) =
      CycleClass.Thom.IntersectionGeometry.supportInDegree X p (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport (show X.carrier ⟶ Y.carrier from f.left) W) := by
  by_cases hW : Y.supportCodimension W = p
  · rw [CycleClass.Thom.IntersectionGeometry.supportInDegree, dite_eq_left hW, ProjectionFormula.Smooth.Cycle.flatMap,
      Finsupp.linearCombination_single, one_smul, cycle_single f m n]
    rw [CycleClass.Thom.IntersectionGeometry.supportInDegree, dite_eq_left ((codimension f m n W).trans hW)]
    rfl
  · rw [CycleClass.Thom.IntersectionGeometry.supportInDegree, dite_eq_right hW, map_zero, CycleClass.Thom.IntersectionGeometry.supportInDegree,
      dite_eq_right (fun h => hW ((codimension f m n W).symm.trans h))]

theorem flatMap_degreeComponent (p : ℕ) (c : Y.carrier →₀ ℚ) :
    ProjectionFormula.Smooth.Cycle.flatMap f p (CyclePushforward.degreeComponent Y p c) =
      CyclePushforward.degreeComponent X p (Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (show X.carrier ⟶ Y.carrier from f.left) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single y a =>
    rw [PushforwardComposition.Grading.degreeComponent_single, map_smul,
      flatMap_supportInDegree f m n]
    change _ = CyclePushforward.degreeComponent X p (Finsupp.mapDomain (Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (show X.carrier ⟶ Y.carrier from f.left))
      (Finsupp.single y a))
    rw [Finsupp.mapDomain_single, PushforwardComposition.Grading.degreeComponent_single,
      Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport_eq_pointClosure]
    simp only [irreducibleSetEquivPoints.apply_symm_apply]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.FiberCycles
