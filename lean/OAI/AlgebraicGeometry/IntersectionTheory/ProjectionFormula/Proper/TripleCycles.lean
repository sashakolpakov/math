import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleLinearExpansion
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperTripleProduct
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowSymmetry

/-! # Triple Cycles -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.TripleCycles

noncomputable section

/-! Proper triple position for finite cycles gives an equality of
successive native intersection cycles, with the grading transported. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical BigOperators

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

def MeetTriply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q t : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) (c : X.RationalDimensionCycle t) : Prop :=
  ∀ A ∈ a.support, ∀ B ∈ b.support, ∀ D ∈ c.support, ∀ E : IrreducibleCloseds X.carrier,
    (E : Set X.carrier) ⊆ ((A.val : Set X.carrier) ∩ B.val) ∩ D.val →
      p + q + t ≤ X.supportCodimension E

theorem meetTriply_swap (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q t : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) (c : X.RationalDimensionCycle t)
    (h : MeetTriply X p q t a b c) : MeetTriply X p t q a c b := by
  intro A hA D hD B hB E hE
  have he := h A hA B hB D hD E (fun x hx => ⟨⟨(hE hx).1.1, (hE hx).2⟩, (hE hx).1.2⟩)
  omega

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q t : ℕ) [SmoothOfRelativeDimension m X.structureMap]

theorem pair_swap (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q)
    (D : X.DimensionCycleSupport t) (hAB : Supports.ProperCycle.pairMeetsProperly X p q A B)
    (hAD : Supports.ProperCycle.pairMeetsProperly X p t A D)
    (ht : ∀ E : IrreducibleCloseds X.carrier,
      (E : Set X.carrier) ⊆ ((A.val : Set X.carrier) ∩ B.val) ∩ D.val →
        p + q + t ≤ X.supportCodimension E) :
    DegreeCast.cycle X (show p + q + t = p + t + q by omega)
      (Supports.ProperCycle.intersectionBilinear X m (p + q) t (Supports.ProperCycle.pairCycle X m p q A B) (Finsupp.single D 1)) =
      Supports.ProperCycle.intersectionBilinear X m (p + t) q (Supports.ProperCycle.pairCycle X m p t A D) (Finsupp.single B 1) := by
  ext C
  rw [DegreeCast.cycle_apply]
  exact ProperTripleProduct.swap_coefficient X m p q t A B D hAB ht hAD _

theorem proper (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle t) (hab : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b)
    (ht : MeetTriply X p q t a b c) :
    CycleClass.Thom.IntersectionGeometry.MeetProperly X (p + q) t (Supports.ProperCycle.intersectionBilinear X m p q a b) c := by
  intro E hE D hD W hW
  obtain ⟨A, hA, B, hB, hE'⟩ := CycleLinearExpansion.support X m p q a b E hE
  have hs := General.RestrictedPrincipalCycle.pair_support X m p q A B (hab A hA B hB) E hE'
  exact ht A hA B hB D hD W (fun x hx => ⟨⟨hs.1 (hW hx).1, hs.2 (hW hx).1⟩, (hW hx).2⟩)

theorem swap (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle t) (hab : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b) (hac : CycleClass.Thom.IntersectionGeometry.MeetProperly X p t a c)
    (ht : MeetTriply X p q t a b c) :
    DegreeCast.cycle X (show p + q + t = p + t + q by omega)
      (Supports.ProperCycle.intersectionBilinear X m (p + q) t (Supports.ProperCycle.intersectionBilinear X m p q a b) c) =
      Supports.ProperCycle.intersectionBilinear X m (p + t) q (Supports.ProperCycle.intersectionBilinear X m p t a c) b := by
  rw [CycleLinearExpansion.nested X m p q t a b c,
    CycleLinearExpansion.nested X m p t q a c b]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro B hB
  rw [pair_swap X m p q t A B D (hab A hA B hB) (hac A hA D hD) (ht A hA B hB D hD)]
  congr 1
  ring

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.TripleCycles
