import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TripleCoefficient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.RestrictedPrincipalCycle

/-! # Proper Triple Product -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperTripleProduct

noncomputable section

section

/-! The coefficient pairing of properly positioned triple intersections
is unchanged when the two successive intersection factors are exchanged. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Symmetry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem sum_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q)
    (hpair : Supports.ProperCycle.pairMeetsProperly X p q A B) (D C : IrreducibleCloseds X.carrier)
    (h : ¬(CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (A.val : Set X.carrier) ∧
      CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (B.val : Set X.carrier) ∧ CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (D : Set X.carrier))) :
    (Supports.ProperCycle.pairCycle X m p q A B).sum (fun E c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X E.val D C) = 0 := by
  apply Finset.sum_eq_zero
  intro E hE
  have hs := General.RestrictedPrincipalCycle.pair_support X m p q A B hpair E hE
  have hz : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X E.val D C = 0 :=
    dite_eq_right (fun hx => h ⟨hs.1 hx.1, hs.2 hx.1, hx.2⟩)
  exact (congrArg (fun z : ℚ => Supports.ProperCycle.pairCycle X m p q A B E * z) hz).trans (mul_zero _)

theorem swap (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q t : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q) (D : X.DimensionCycleSupport t)
    (hAB : Supports.ProperCycle.pairMeetsProperly X p q A B) (hAD : Supports.ProperCycle.pairMeetsProperly X p t A D)
    (htriple : ∀ E : IrreducibleCloseds X.carrier,
      (E : Set X.carrier) ⊆ ((A.val : Set X.carrier) ∩ B.val) ∩ D.val → p + q + t ≤ X.supportCodimension E)
    (C : X.DimensionCycleSupport (p + q + t)) :
    (Supports.ProperCycle.pairCycle X m p q A B).sum (fun E c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X E.val D.val C.val) =
      (Supports.ProperCycle.pairCycle X m p t A D).sum (fun E c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X E.val B.val C.val) := by
  by_cases hx : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier) ∧
      CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (B.val : Set X.carrier) ∧ CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (D.val : Set X.carrier)
  · let C' : X.DimensionCycleSupport (p + t + q) := ⟨C.val, by rw [C.property]; omega⟩
    have ht : ∀ E : IrreducibleCloseds X.carrier,
        (E : Set X.carrier) ⊆ ((A.val : Set X.carrier) ∩ D.val) ∩ B.val → p + t + q ≤ X.supportCodimension E := by
      intro E hE
      have h := htriple E (fun z hz => ⟨⟨(hE hz).1.1, (hE hz).2⟩, (hE hz).1.2⟩)
      omega
    calc
      _ = IteratedTorEuler.euler (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
          (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier D.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx.2.2)
          (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx.2.1)
          (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx.1) m m :=
        (TripleCoefficient.euler_eq_pair_sum X m p q t A B D hAB htriple C hx.1 hx.2.1 hx.2.2).symm
      _ = _ := (TripleSupportEuler.commute X m (p + q + t) A.val B.val D.val htriple C hx.1 hx.2.1 hx.2.2).trans
        (TripleCoefficient.euler_eq_pair_sum X m p t q A D B hAD ht C' hx.1 hx.2.2 hx.2.1)
  · rw [sum_zero X m p q A B hAB D.val C.val hx,
      sum_zero X m p t A D hAD B.val C.val (fun h => hx ⟨h.1, h.2.2, h.2.1⟩)]

end Symmetry

end

/-! Properly positioned triple supports give actual successive
intersection cycles with symmetric coefficients. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q t : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q) (D : X.DimensionCycleSupport t)
  (hAB : Supports.ProperCycle.pairMeetsProperly X p q A B)
  (htriple : ∀ E : IrreducibleCloseds X.carrier,
    (E : Set X.carrier) ⊆ ((A.val : Set X.carrier) ∩ B.val) ∩ D.val → p + q + t ≤ X.supportCodimension E)

include hAB htriple in
theorem proper : CycleClass.Thom.IntersectionGeometry.MeetProperly X (p + q) t (Supports.ProperCycle.pairCycle X m p q A B) (Finsupp.single D 1) := by
  intro E hE D' hD'
  have he : D' = D := by simpa using hD'
  subst D'
  have hs := General.RestrictedPrincipalCycle.pair_support X m p q A B hAB E hE
  intro W hW
  exact htriple W (fun x hx => ⟨⟨hs.1 (hW hx).1, hs.2 (hW hx).1⟩, (hW hx).2⟩)

include hAB htriple in
theorem coefficient (C : X.DimensionCycleSupport (p + q + t)) :
    Supports.ProperCycle.intersectionBilinear X m (p + q) t (Supports.ProperCycle.pairCycle X m p q A B) (Finsupp.single D 1) C =
      (Supports.ProperCycle.pairCycle X m p q A B).sum (fun E c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X E.val D.val C.val) := by
  have h := (Supports.ProperCycle.intersectionBilinear_isProper X m (p + q) t _ _
    (proper X m p q t A B D hAB htriple)).2 C
  simpa only [Finsupp.sum_single_index, mul_zero, zero_mul, mul_one] using h

include hAB htriple in
theorem swap_coefficient (hAD : Supports.ProperCycle.pairMeetsProperly X p t A D) (C : X.DimensionCycleSupport (p + q + t)) :
    Supports.ProperCycle.intersectionBilinear X m (p + q) t (Supports.ProperCycle.pairCycle X m p q A B) (Finsupp.single D 1) C =
      Supports.ProperCycle.intersectionBilinear X m (p + t) q (Supports.ProperCycle.pairCycle X m p t A D) (Finsupp.single B 1)
        ⟨C.val, by rw [C.property]; omega⟩ := by
  have ht : ∀ E : IrreducibleCloseds X.carrier,
      (E : Set X.carrier) ⊆ ((A.val : Set X.carrier) ∩ D.val) ∩ B.val → p + t + q ≤ X.supportCodimension E := by
    intro E hE
    have h := htriple E (fun x hx => ⟨⟨(hE hx).1.1, (hE hx).2⟩, (hE hx).1.2⟩)
    omega
  rw [coefficient X m p q t A B D hAB htriple C,
    coefficient X m p t q A D B hAD ht]
  exact Symmetry.swap X m p q t A B D hAB hAD htriple C

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperTripleProduct
