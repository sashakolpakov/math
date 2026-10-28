import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowZero
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeFiltrationEuler

/-! # Right Zero -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RightZero

noncomputable section

/-! The exact Chow intersection is bilinear also when its second input
has codimension zero. This is the order used by graph pullback in degree zero. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical BigOperators

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Action

theorem euler_unit_right (R : Type) [CommRing R] (M N : ModuleCat R)
    (e : N ≃ₗ[R] R) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (Module.length R (((Tor (ModuleCat R) i).obj M).obj N)).toNat) =
      (Module.length R M).toNat := by
  calc
    _ = ProjectionFormula.Tor.Euler.euler R M (.of R R) d := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun a : ℕ∞ => (-1 : ℚ) ^ i * (a.toNat : ℚ))
        (((Tor (ModuleCat R) i).obj M).mapIso e.toModuleIso).toLinearEquiv.length_eq
    _ = _ := PrimeFiltrationEuler.euler_unit_right R M d

theorem multiplicity_zero_right (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A C : X.DimensionCycleSupport p)
    (B : X.DimensionCycleSupport 0) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val C.val =
      if A = C ∧ C.val ≤ B.val then 1 else 0 := by
  by_cases h : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier) ∩ (B.val : Set X.carrier)
  · have hCA := (Supports.supportPoint_mem_iff_subset
      ⟨A.val, A.val.isClosed⟩ C.val).mp h.1
    have hCB := (Supports.supportPoint_mem_iff_subset
      ⟨B.val, B.val.isClosed⟩ C.val).mp h.2
    have he : A = C := Subtype.ext (IntersectionZero.eq_of_subset_of_codimension_eq X m hCA
      (C.property.trans A.property.symm)).symm
    subst A
    rw [ite_eq_left ⟨rfl, hCB⟩, CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_left h]
    let : IsOpenImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι B.val) := Open.Support.inclusion_isOpenImmersion
      B.val (Open.Support.codimension_zero_isOpen X m B)
    change (∑ i ∈ Finset.range (X.ambientDimension + 1), (-1 : ℚ) ^ i *
      (Module.length (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
        (((Tor (ModuleCat (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))) i).obj
          (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier C.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) h.1)).obj
            (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) h.2))).toNat) = 1
    rw [euler_unit_right _ _ _ (Open.Support.localModuleEquiv B.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) h.2)]
    simp [Open.Support.localModule_length_at_generic]
  · rw [CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_right h, ite_eq_right]
    rintro ⟨rfl, hCB⟩
    have hc : CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ (A.val : Set X.carrier) :=
      (A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem
    exact h ⟨hc, hCB hc⟩

def cycleIntersection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    X.RationalDimensionCycle p →ₗ[ℚ] X.RationalDimensionCycle 0 →ₗ[ℚ]
      X.RationalDimensionCycle (p + 0) := (Component.Action.cycleAction X p).flip

theorem cycleIntersection_isProper (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle 0) :
    CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X p 0 a b (cycleIntersection X p a b) := by
  refine ⟨?_, ?_⟩
  · intro A _ B _ C hC
    have hCA : C ≤ A.val := fun x hx => (hC hx).1
    have h := (Supports.codimension_strictAnti X m).antitone hCA
    simpa only [A.property, add_zero] using h
  · intro C
    change Component.Action.cycleAction X p b a C = _
    rw [Component.Action.cycleAction_apply]
    change _ = ∑ A ∈ a.support, ∑ B ∈ b.support,
      a A * b B * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val C.val
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro B _
    simp only [multiplicity_zero_right X m p]
    change b B * (if C.val ≤ B.val then a C else 0) = _
    by_cases hC : C.val ≤ B.val
    · simp only [hC, and_true, mul_ite, mul_one, mul_zero, ite_true]
      rw [Finset.sum_ite_eq']
      by_cases ha : C ∈ a.support
      · simp [ha, mul_comm]
      · have hz : a C = 0 := Finsupp.notMem_support_iff.mp ha
        simp [ha, hz]
    · simp [hC]

def chowIntersectionMap (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] :
    ProperCycleLinearity.ChowQ X p →ₗ[ℚ] ProperCycleLinearity.ChowQ X 0 →ₗ[ℚ] ProperCycleLinearity.ChowQ X (p + 0) :=
  (ChowZero.chowAction X m p).flip

theorem chowIntersectionMap_mk (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle 0) :
    chowIntersectionMap X m p (ProperCycleLinearity.cycleToChowQ X p a) (ProperCycleLinearity.cycleToChowQ X 0 b) =
      ProperCycleLinearity.cycleToChowQ X (p + 0) (cycleIntersection X p a b) := rfl

theorem representsIntersection_iff (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle 0)
    (c : X.RationalDimensionCycle (p + 0)) :
    CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X p 0 a b c ↔ ProperCycleLinearity.cycleToChowQ X (p + 0) c =
      chowIntersectionMap X m p (ProperCycleLinearity.cycleToChowQ X p a) (ProperCycleLinearity.cycleToChowQ X 0 b) := by
  constructor
  · rintro ⟨a', b', c', ha, hb, hp, hc⟩
    rw [(ProperCycleLinearity.cycleToChowQ_eq_iff X p a a').mpr ha,
      (ProperCycleLinearity.cycleToChowQ_eq_iff X 0 b b').mpr hb, chowIntersectionMap_mk,
      (ProperCycleLinearity.cycleToChowQ_eq_iff X (p + 0) c c').mpr hc]
    exact congrArg (ProperCycleLinearity.cycleToChowQ X (p + 0))
      (CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X p 0 hp (cycleIntersection_isProper X m p a' b'))
  · intro h
    refine ⟨a, b, cycleIntersection X p a b, CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X p a,
      CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X 0 b, cycleIntersection_isProper X m p a b, ?_⟩
    apply (ProperCycleLinearity.cycleToChowQ_eq_iff X (p + 0) c (cycleIntersection X p a b)).mp
    exact h.trans (chowIntersectionMap_mk X m p a b)

theorem chowIntersection_eq_singleton (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (a : ProperCycleLinearity.ChowQ X p) (b : ProperCycleLinearity.ChowQ X 0) :
    ProperCycleLinearity.chowIntersection X p 0 a b = {chowIntersectionMap X m p a b} := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X p a
  obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X 0 b
  ext c
  obtain ⟨c, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X (p + 0) c
  rw [ProperCycleLinearity.chowIntersection_mk_iff, Set.mem_singleton_iff, representsIntersection_iff X m p]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RightZero
