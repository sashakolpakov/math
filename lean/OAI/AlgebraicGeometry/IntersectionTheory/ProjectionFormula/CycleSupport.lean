import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

/-! # Cycle Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleSupport

noncomputable section

/-! Native proper intersections and native proper pushforward preserve
the expected closed supports. These coefficient statements retain exact
finite cycles before passing to rational equivalence. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

def SupportedOn (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (a : X.RationalDimensionCycle p) (S : Closeds X.carrier) : Prop :=
  ∀ A ∈ a.support, (A.val : Set X.carrier) ⊆ S

theorem proper_intersection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle (p + q)) (hc : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X p q a b c)
    (S : Closeds X.carrier) (ha : SupportedOn X p a S) : SupportedOn X (p + q) c S := by
  intro C hC
  apply (Supports.supportPoint_mem_iff_subset S C.val).mp
  by_contra hn
  have hz : c C = 0 := by
    rw [hc.2 C]
    apply Finset.sum_eq_zero
    intro A hA
    apply Finset.sum_eq_zero
    intro B _
    have hi : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val C.val = 0 :=
      dite_eq_right (fun h => hn (ha A hA h.1))
    change a A * b B * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val C.val = 0
    rw [hi, mul_zero]
  exact (Finsupp.mem_support_iff.mp hC) hz

theorem pushforward (X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (f : X.toOver ⟶ Y.toOver) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (S : Closeds X.carrier) (T : Closeds Y.carrier)
    (ha : SupportedOn X p a S)
    (hST : (fun x : X.carrier => (f.left x : Y.carrier)) '' (S : Set X.carrier) ⊆ (T : Set Y.carrier)) :
    SupportedOn Y q (ProperCycleLinearity.cyclePushforward f p q a) T := by
  intro B hB
  apply (Supports.supportPoint_mem_iff_subset T B.val).mp
  by_contra hn
  have hz : ProperCycleLinearity.cyclePushforward f p q a B = 0 := by
    simp only [ProperCycleLinearity.cyclePushforward, Finsupp.linearCombination_apply, Finsupp.sum,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, ProperCycleLinearity.cyclePushforwardGenerator_apply]
    apply Finset.sum_eq_zero
    intro A hA
    have hne : ProperCycleLinearity.imageSupport f A.val ≠ B.val := by
      intro he
      have hp : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val := by
        have hh := congrArg CycleClass.Thom.IntersectionGeometry.supportPoint he
        change irreducibleSetEquivPoints (irreducibleSetEquivPoints.symm (f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val))) = _ at hh
        exact (irreducibleSetEquivPoints.apply_symm_apply _).symm.trans hh
      exact hn (hp ▸ hST ⟨CycleClass.Thom.IntersectionGeometry.supportPoint A.val,
        ha A hA ((A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem), rfl⟩)
    rw [ite_eq_right hne, smul_zero]
  exact (Finsupp.mem_support_iff.mp hB) hz

theorem singleton (Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (q : ℕ) (B : Y.DimensionCycleSupport q)
    (hclosed : IsClosed ({CycleClass.Thom.IntersectionGeometry.supportPoint B.val} : Set Y.carrier))
    (a : Y.RationalDimensionCycle q) (h : SupportedOn Y q a ⟨{CycleClass.Thom.IntersectionGeometry.supportPoint B.val}, hclosed⟩) :
    a = Finsupp.single B (a B) := by
  ext C
  by_cases he : B = C
  · subst C
    rw [Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne' he]
    by_contra hc
    have hh := h C (Finsupp.mem_support_iff.mpr hc)
      ((C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed).mem)
    exact he (Subtype.ext (irreducibleSetEquivPoints.injective (Set.mem_singleton_iff.mp hh).symm))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleSupport
