import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.SerreVanishing
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalParameterWeightDimension

/-! # Expected Component Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExpectedComponentCycle

noncomputable section

/-! The expected-codimension component cycle is defined for every
pair of supports. Serre vanishing removes excess components from the
principal-weight formula, without assuming the pair meets properly. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
  (A : X.DimensionCycleSupport p) (W : X.DimensionCycleSupport k)

abbrev components := Finite.ClosedComponents.components X.carrier
  (IsolatedGeometricComponents.intersection X.carrier W.val A.val)

def ambient : IrreducibleCloseds X.carrier →₀ ℚ :=
  Finsupp.onFinset (components X p k A W)
    (fun D => if D ∈ components X p k A W then
      TotalTorCoefficient.coefficient X.carrier W.val A.val (CycleClass.Thom.IntersectionGeometry.supportPoint D) m else 0)
    (by intro D h; by_contra hn; exact h (ite_eq_right hn))

def cycle : X.RationalDimensionCycle (p + k) :=
  Finsupp.comapDomain Subtype.val (ambient X m p k A W) Subtype.val_injective.injOn

theorem apply (D : X.DimensionCycleSupport (p + k)) :
    cycle X m p k A W D = if D.val ∈ components X p k A W then
      TotalTorCoefficient.coefficient X.carrier W.val A.val (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) m else 0 := rfl

theorem mem_components (D : X.DimensionCycleSupport (p + k))
    (hD : D ∈ (cycle X m p k A W).support) : D.val ∈ components X p k A W := by
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hD) (by rw [ExpectedComponentCycle.apply, ite_eq_right hn])

theorem support_subset (D : X.DimensionCycleSupport (p + k))
    (hD : D ∈ (cycle X m p k A W).support) : D.val ≤ A.val ∧ D.val ≤ W.val := by
  have h := Finite.ClosedComponents.subset X.carrier
    (IsolatedGeometricComponents.intersection X.carrier W.val A.val) D.val
    (mem_components X m p k A W D hD)
  exact ⟨fun _ hy => (h hy).2, fun _ hy => (h hy).1⟩

variable [SmoothOfRelativeDimension m X.structureMap]

theorem reindex (C : X.DimensionCycleSupport (p + (k + 1)))
    (r s : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) :
    (∑ D ∈ components X p k A W,
      TotalTorCoefficient.coefficient X.carrier W.val A.val (CycleClass.Thom.IntersectionGeometry.supportPoint D) m *
        (GlobalParameterSum.Weights.weight X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) r D -
          GlobalParameterSum.Weights.weight X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) s D)) =
      (cycle X m p k A W).sum (fun D c => c *
        (GlobalParameterSum.Weights.weight X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) r D.val -
          GlobalParameterSum.Weights.weight X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) s D.val)) := by
  let c := cycle X m p k A W
  let F := components X p k A W
  let T := c.support.image Subtype.val
  let w := fun D : IrreducibleCloseds X.carrier =>
    GlobalParameterSum.Weights.weight X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) r D -
      GlobalParameterSum.Weights.weight X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) s D
  have hc (D : X.DimensionCycleSupport (p + k)) (hD : D.val ∈ F) :
      TotalTorCoefficient.coefficient X.carrier W.val A.val (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) m = c D := by
    rw [ExpectedComponentCycle.apply, ite_eq_left hD]
  have hT : T ⊆ F := by
    intro D hD
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hD
    exact mem_components X m p k A W E hE
  have hsum : (∑ D ∈ T, TotalTorCoefficient.coefficient X.carrier W.val A.val (CycleClass.Thom.IntersectionGeometry.supportPoint D) m * w D) =
      ∑ D ∈ F, TotalTorCoefficient.coefficient X.carrier W.val A.val (CycleClass.Thom.IntersectionGeometry.supportPoint D) m * w D := by
    apply Finset.sum_subset hT
    intro D hDF hDT
    by_cases hdim : X.supportCodimension D = p + k
    · let E : X.DimensionCycleSupport (p + k) := ⟨D, hdim⟩
      have hE : E ∉ c.support := fun h => hDT (Finset.mem_image.mpr ⟨E, h, rfl⟩)
      rw [hc E hDF, Finsupp.notMem_support_iff.mp hE, zero_mul]
    · by_cases hlow : X.supportCodimension D < p + k
      · have hd : X.supportCodimension D < X.supportCodimension W.val + X.supportCodimension A.val := by
          rw [W.property, A.property]
          omega
        rw [Component.SerreVanishing.zero X m W.val A.val D hDF hd, zero_mul]
      · have hd : X.supportCodimension C.val ≤ X.supportCodimension D := by rw [C.property]; omega
        have hw : w D = 0 := by
          dsimp only [w]
          rw [GlobalParameterWeightDimension.vanishes X m C.val D hd r,
            GlobalParameterWeightDimension.vanishes X m C.val D hd s, sub_self]
        rw [hw, mul_zero]
  change (∑ D ∈ F, _ * w D) = c.sum (fun D a => a * w D.val)
  rw [← hsum, Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
  apply Finset.sum_congr rfl
  intro D hD
  rw [hc D (mem_components X m p k A W D hD)]

theorem reindex_at (C : X.DimensionCycleSupport (p + (k + 1)))
    (x : X.carrier) (hx : x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val) (r s : X.carrier.presheaf.stalk x) :
    (∑ D ∈ components X p k A W,
      TotalTorCoefficient.coefficient X.carrier W.val A.val (CycleClass.Thom.IntersectionGeometry.supportPoint D) m *
        (GlobalParameterSum.Weights.weight X.carrier x r D - GlobalParameterSum.Weights.weight X.carrier x s D)) =
      (cycle X m p k A W).sum (fun D c => c *
        (GlobalParameterSum.Weights.weight X.carrier x r D.val - GlobalParameterSum.Weights.weight X.carrier x s D.val)) := by
  subst x
  exact reindex X m p k A W C r s

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExpectedComponentCycle
