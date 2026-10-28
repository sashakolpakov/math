import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports

/-! # Intersection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Proper.Intersection

noncomputable section

/-! Properly meeting cycles have an actual finite intersection cycle
with exactly ThomClass's local Tor coefficients. The finite construction is
bilinear before imposing the proper-meeting condition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical BigOperators

def pairMeetsProperly (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q) : Prop :=
  ∀ C : IrreducibleCloseds X.carrier,
    (C : Set X.carrier) ⊆ (A.val : Set X.carrier) ∩ (B.val : Set X.carrier) →
      p + q ≤ X.supportCodimension C

theorem pair_coefficients_finite (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q)
    (h : pairMeetsProperly X p q A B) :
    (Function.support (fun C : X.DimensionCycleSupport (p + q) =>
      IntersectionGeometry.intersectionMultiplicity X A.val B.val C.val)).Finite := by
  let S : Closeds X.carrier := ⟨(A.val : Set X.carrier) ∩ B.val, A.val.isClosed.inter B.val.isClosed⟩
  apply (Intersection.Supports.finite_supports_in_proper_closed X (p + q) S h).subset
  intro C hC
  by_contra hc
  exact hC (dite_eq_right hc)

def pairCycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q) :
    X.RationalDimensionCycle (p + q) :=
  if h : pairMeetsProperly X p q A B then
    Finsupp.ofSupportFinite (fun C => IntersectionGeometry.intersectionMultiplicity X A.val B.val C.val)
      (pair_coefficients_finite X p q A B h)
  else 0

theorem pairCycle_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q)
    (h : pairMeetsProperly X p q A B) (C : X.DimensionCycleSupport (p + q)) :
    pairCycle X p q A B C = IntersectionGeometry.intersectionMultiplicity X A.val B.val C.val := by
  rw [pairCycle, dite_eq_left h]
  rfl

def intersectionBilinear (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ) :
    X.RationalDimensionCycle p →ₗ[ℚ] X.RationalDimensionCycle q →ₗ[ℚ]
      X.RationalDimensionCycle (p + q) :=
  Finsupp.linearCombination ℚ (fun A => Finsupp.linearCombination ℚ (pairCycle X p q A))

theorem intersectionBilinear_isProper (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (h : IntersectionGeometry.MeetProperly X p q a b) :
    IntersectionGeometry.IsProperIntersectionCycle X p q a b (intersectionBilinear X p q a b) := by
  refine ⟨h, ?_⟩
  intro C
  simp only [intersectionBilinear, Finsupp.linearCombination_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro B hB
  rw [pairCycle_apply X p q A B (h A hA B hB) C]
  ring

theorem properIntersection_exists_unique (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (h : IntersectionGeometry.MeetProperly X p q a b) :
    ∃! c : X.RationalDimensionCycle (p + q), IntersectionGeometry.IsProperIntersectionCycle X p q a b c := by
  refine ⟨intersectionBilinear X p q a b, intersectionBilinear_isProper X p q a b h, ?_⟩
  intro c hc
  exact IntersectionGeometry.isProperIntersectionCycle_unique X p q hc (intersectionBilinear_isProper X p q a b h)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Proper.Intersection
