import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Symmetry
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast

/-! # Chow Symmetry -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowSymmetry

noncomputable section

section

/-! Symmetry of the native Tor intersection in arbitrary
codimensions, with explicit transport of the sum grading. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Graded

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast

theorem cycle_symm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {p q : ℕ} (h : p = q)
    (a : X.RationalDimensionCycle p) : DegreeCast.cycle X h.symm (DegreeCast.cycle X h a) = a := by
  subst q
  rfl

theorem rationallyEquivalent_cast (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {p q : ℕ} (h : p = q)
    (a b : X.RationalDimensionCycle p) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X q (DegreeCast.cycle X h a) (DegreeCast.cycle X h b) ↔ CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a b := by
  subst q
  rfl

theorem meetProperly_comm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b ↔ CycleClass.Thom.IntersectionGeometry.MeetProperly X q p b a := by
  constructor <;> intro h A hA B hB C hC
  · simpa only [Nat.add_comm] using h B hB A hA C (by simpa only [Set.inter_comm] using hC)
  · simpa only [Nat.add_comm] using h B hB A hA C (by simpa only [Set.inter_comm] using hC)

theorem proper_cycle_comm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle (p + q)) (hc : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X p q a b c) :
    CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X q p b a (DegreeCast.cycle X (Nat.add_comm p q) c) := by
  refine ⟨(meetProperly_comm X p q a b).mp hc.1, ?_⟩
  intro C
  rw [DegreeCast.cycle_apply, hc.2]
  simp only [Finsupp.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro A _
  change a A * b B * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val C.val =
    b B * a A * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val
  rw [Symmetry.multiplicity_comm, mul_comm (a A) (b B)]

theorem represents_comm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle (p + q)) :
    CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X p q a b c ↔
      CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X q p b a (DegreeCast.cycle X (Nat.add_comm p q) c) := by
  have hf {r s : ℕ} (u : X.RationalDimensionCycle r) (v : X.RationalDimensionCycle s)
      (w : X.RationalDimensionCycle (r + s)) (h : CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X r s u v w) :
      CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X s r v u (DegreeCast.cycle X (Nat.add_comm r s) w) := by
    obtain ⟨u', v', w', hu, hv, hp, hw⟩ := h
    exact ⟨v', u', DegreeCast.cycle X (Nat.add_comm r s) w', hv, hu,
      proper_cycle_comm X r s u' v' w' hp,
      (rationallyEquivalent_cast X (Nat.add_comm r s) w w').mpr hw⟩
  constructor
  · exact hf a b c
  · intro h
    have he := hf b a (DegreeCast.cycle X (Nat.add_comm p q) c) h
    have hh : DegreeCast.cycle X (Nat.add_comm q p) (DegreeCast.cycle X (Nat.add_comm p q) c) = c :=
      cycle_symm X (Nat.add_comm p q) c
    rwa [hh] at he

theorem pair_comm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q) :
    DegreeCast.cycle X (Nat.add_comm p q) (Supports.ProperCycle.pairCycle X m p q A B) = Supports.ProperCycle.pairCycle X m q p B A := by
  have hp : Supports.ProperCycle.pairMeetsProperly X p q A B ↔ Supports.ProperCycle.pairMeetsProperly X q p B A := by
    simp only [Supports.ProperCycle.pairMeetsProperly, Set.inter_comm, Nat.add_comm]
  by_cases h : Supports.ProperCycle.pairMeetsProperly X p q A B
  · ext C
    rw [DegreeCast.cycle_apply, Supports.ProperCycle.pairCycle_apply X m p q A B h,
      Supports.ProperCycle.pairCycle_apply X m q p B A (hp.mp h)]
    exact Symmetry.multiplicity_comm X A.val B.val C.val
  · rw [Supports.ProperCycle.pairCycle, dite_eq_right h, map_zero, Supports.ProperCycle.pairCycle, dite_eq_right (fun h' => h (hp.mpr h'))]

theorem bilinear_comm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    DegreeCast.cycle X (Nat.add_comm p q) (Supports.ProperCycle.intersectionBilinear X m p q a b) =
      Supports.ProperCycle.intersectionBilinear X m q p b a := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | single A r =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b b' hb hb' => simp only [map_add, LinearMap.add_apply, hb, hb']
    | single B s =>
      simp only [Supports.ProperCycle.intersectionBilinear, Finsupp.linearCombination_single, LinearMap.smul_apply,
        map_smul, smul_smul]
      rw [pair_comm X m p q A B, mul_comm]

end Graded

end

/-! Native intersection relations and exact bilinear maps transport
under exchange of the two codimensions. -/

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast

theorem chow_symm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {p q : ℕ} (h : p = q)
    (a : ProperCycleLinearity.ChowQ X p) : DegreeCast.chow X h.symm (DegreeCast.chow X h a) = a := by
  subst q
  rfl

theorem mem_comm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : ProperCycleLinearity.ChowQ X p) (b : ProperCycleLinearity.ChowQ X q) (c : ProperCycleLinearity.ChowQ X (p + q)) :
    c ∈ ProperCycleLinearity.chowIntersection X p q a b ↔
      DegreeCast.chow X (Nat.add_comm p q) c ∈ ProperCycleLinearity.chowIntersection X q p b a := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X p a
  obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X q b
  obtain ⟨c, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X (p + q) c
  rw [DegreeCast.chow_mk, ProperCycleLinearity.chowIntersection_mk_iff, ProperCycleLinearity.chowIntersection_mk_iff]
  exact Graded.represents_comm X p q a b c

theorem reverse_map_exists (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (I : ProperCycleLinearity.ChowQ X p →ₗ[ℚ] ProperCycleLinearity.ChowQ X q →ₗ[ℚ] ProperCycleLinearity.ChowQ X (p + q))
    (hI : ∀ a b, ProperCycleLinearity.chowIntersection X p q a b = {I a b}) :
    ∃ J : ProperCycleLinearity.ChowQ X q →ₗ[ℚ] ProperCycleLinearity.ChowQ X p →ₗ[ℚ] ProperCycleLinearity.ChowQ X (q + p),
      ∀ b a, ProperCycleLinearity.chowIntersection X q p b a = {J b a} := by
  refine ⟨I.flip.compr₂ (DegreeCast.chow X (Nat.add_comm p q)).toLinearMap, ?_⟩
  intro b a
  ext c
  rw [mem_comm X q p b a c, hI, Set.mem_singleton_iff, Set.mem_singleton_iff]
  change DegreeCast.chow X (Nat.add_comm q p) c = I a b ↔ c = DegreeCast.chow X (Nat.add_comm p q) (I a b)
  constructor
  · intro h
    have he := congrArg (DegreeCast.chow X (Nat.add_comm p q)) h
    exact (chow_symm X (Nat.add_comm q p) c).symm.trans he
  · intro h
    rw [h]
    exact chow_symm X (Nat.add_comm p q) (I a b)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowSymmetry
