import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.FiberDegree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.EtaleSupportPoints
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardCoefficientCongruence

/-! # Fiber Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.FiberCycle

noncomputable section

/-! Native fiber points parameterize the graded supports contributing
to one pushforward coefficient. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
  (m n k l : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
  (hd : k + n = l + m) (W : IrreducibleCloseds X.carrier) (U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens)
  [Etale (U.ι ≫ Map.supportImageMap f W)] (y : CycleClass.Geometric.GenericPoint.reducedSupportScheme (ProperCycleLinearity.imageSupport f W))
  (hy : y ∈ Proper.EtaleRestriction.good (Map.supportImageMap f W) U)
  (D : Y.DimensionCycleSupport l) (hpoint : CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W) y = CycleClass.Thom.IntersectionGeometry.supportPoint D.val)

include hpoint in
omit [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
  [Etale (U.ι ≫ Map.supportImageMap f W)] in
theorem point_image (x : (Map.supportImageMap f W) ⁻¹' {y}) :
    f.left (CycleClass.Geometric.GenericPoint.reducedSupportι W x.val) = CycleClass.Thom.IntersectionGeometry.supportPoint D.val := by
  have h := congrArg (fun g : CycleClass.Geometric.GenericPoint.reducedSupportScheme W ⟶ Y.carrier => g x.val)
    (Map.supportImageMap_inclusion f W)
  exact h.symm.trans ((congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W))
    (show Map.supportImageMap f W x.val = y from x.property)).trans hpoint)

def support (x : (Map.supportImageMap f W) ⁻¹' {y}) : X.DimensionCycleSupport k :=
  ⟨irreducibleSetEquivPoints.symm (CycleClass.Geometric.GenericPoint.reducedSupportι W x.val),
    Finite.EtaleSupportPoints.codimension f m n k l hd W U x.val
      (by rw [show Map.supportImageMap f W x.val = y from x.property]; exact hy)
      D (point_image f l W y D hpoint x)⟩

theorem support_point (x : (Map.supportImageMap f W) ⁻¹' {y}) :
    CycleClass.Thom.IntersectionGeometry.supportPoint (support f m n k l hd W U y hy D hpoint x).val = CycleClass.Geometric.GenericPoint.reducedSupportι W x.val :=
  irreducibleSetEquivPoints.apply_symm_apply _

theorem support_mem (x : (Map.supportImageMap f W) ⁻¹' {y}) :
    CycleClass.Thom.IntersectionGeometry.supportPoint (support f m n k l hd W U y hy D hpoint x).val ∈ (W : Set X.carrier) := by
  rw [support_point, ← CycleClass.Geometric.GenericPoint.range_reducedSupportι W]
  exact ⟨x.val, rfl⟩

theorem support_image (x : (Map.supportImageMap f W) ⁻¹' {y}) :
    ProperCycleLinearity.imageSupport f (support f m n k l hd W U y hy D hpoint x).val = D.val := by
  apply irreducibleSetEquivPoints.injective
  change irreducibleSetEquivPoints (irreducibleSetEquivPoints.symm _) = CycleClass.Thom.IntersectionGeometry.supportPoint D.val
  rw [irreducibleSetEquivPoints.apply_symm_apply, support_point]
  exact point_image f l W y D hpoint x

theorem support_injective : Function.Injective (support f m n k l hd W U y hy D hpoint) := by
  intro a b h
  apply Subtype.ext
  apply (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective
  exact (support_point f m n k l hd W U y hy D hpoint a).symm.trans
    ((congrArg (fun C : X.DimensionCycleSupport k => CycleClass.Thom.IntersectionGeometry.supportPoint C.val) h).trans
      (support_point f m n k l hd W U y hy D hpoint b))

theorem support_cover (C : X.DimensionCycleSupport k)
    (hC : ProperCycleLinearity.imageSupport f C.val = D.val) (hCW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W : Set X.carrier)) :
    ∃ x, support f m n k l hd W U y hy D hpoint x = C := by
  let x := CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hCW
  have hx : Map.supportImageMap f W x = y := by
    apply (CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W)).isClosedEmbedding.injective
    have he := congrArg (fun g : CycleClass.Geometric.GenericPoint.reducedSupportScheme W ⟶ Y.carrier => g x)
      (Map.supportImageMap_inclusion f W)
    change CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W) (Map.supportImageMap f W x) = f.left (CycleClass.Geometric.GenericPoint.reducedSupportι W x) at he
    change CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W) (Map.supportImageMap f W x) = CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W) y
    rw [he, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec, hpoint]
    have hi := congrArg CycleClass.Thom.IntersectionGeometry.supportPoint hC
    exact (irreducibleSetEquivPoints.apply_symm_apply _).symm.trans hi
  refine ⟨⟨x, hx⟩, Subtype.ext (irreducibleSetEquivPoints.injective ?_)⟩
  exact (support_point f m n k l hd W U y hy D hpoint ⟨x, hx⟩).trans (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W _ hCW)

include hd hy hpoint in
theorem coefficient (c : X.RationalDimensionCycle k) (r : ℚ)
    (hc : ∀ C : X.DimensionCycleSupport k, ProperCycleLinearity.imageSupport f C.val = D.val →
      c C = if CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W : Set X.carrier) then r else 0) :
    ProperCycleLinearity.cyclePushforward f k l c D = r * (f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint W) : ℚ) := by
  let F := (Map.supportImageMap f W) ⁻¹' {y}
  let : Fintype F := (FiberDegree.finite f W U y hy).fintype
  let v : F → X.DimensionCycleSupport k := support f m n k l hd W U y hy D hpoint
  let b : X.RationalDimensionCycle k := ∑ x : F, Finsupp.single (v x) r
  have hb : ∀ C : X.DimensionCycleSupport k, ProperCycleLinearity.imageSupport f C.val = D.val → c C = b C := by
    intro C hC
    rw [hc C hC]
    change _ = (∑ x : F, Finsupp.single (v x) r) C
    rw [Finsupp.finsetSum_apply]
    by_cases hCW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W : Set X.carrier)
    · rw [ite_eq_left hCW]
      obtain ⟨x, hx⟩ := support_cover f m n k l hd W U y hy D hpoint C hC hCW
      symm
      rw [Finset.sum_eq_single x]
      · rw [show v x = C from hx, Finsupp.single_eq_same]
      · intro z _ hzx
        apply Finsupp.single_eq_of_ne'
        exact fun hz => hzx (support_injective f m n k l hd W U y hy D hpoint (hz.trans hx.symm))
      · simp
    · rw [ite_eq_right hCW]
      symm
      apply Finset.sum_eq_zero
      intro x _
      apply Finsupp.single_eq_of_ne'
      intro hx
      exact hCW (hx ▸ support_mem f m n k l hd W U y hy D hpoint x)
  rw [PushforwardCoefficientCongruence.eq f k l c b D hb]
  change ProperCycleLinearity.cyclePushforward f k l (∑ x : F, Finsupp.single (v x) r) D = _
  simp only [map_sum, Finsupp.finsetSum_apply, ProperCycleLinearity.cyclePushforward_single, Finsupp.smul_apply,
    ProperCycleLinearity.cyclePushforwardGenerator_apply, support_image, ite_true, smul_eq_mul, v, support_point]
  rw [← Finset.mul_sum, ← Nat.cast_sum, FiberDegree.sum f W U y hy]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.FiberCycle
