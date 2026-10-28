import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.SumComparison
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ChowMoving

/-! # Integral -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Integral

noncomputable section

section

/-! Intersecting a rational principal divisor with a divisor on which
its defining function has order zero gives the actual principal divisor
of the restricted function. Hence this intersection is rationally zero. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Divisor

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

theorem exists_principal_intersection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (A : X.DimensionCycleSupport 1) (f : X.carrier.functionField) (hf : f ≠ 0)
    (hord : X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = 0)
    (d : X.RationalDimensionCycle 1)
    (hd : ∀ B : X.DimensionCycleSupport 1, d B = (X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) : ℚ)) :
    ∃ g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val).functionField, g ≠ 0 ∧
      CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 1 d (Finsupp.single A 1) (ClosedSectionCycle.principalCycle X 2 A.val g) := by
  obtain ⟨g, hg, hlocal⟩ := RestrictedDivisorOrder.exists_restriction X m A f hf hord
  refine ⟨g, hg, ?_, ?_⟩
  · apply Divisor.ChowMoving.meetProperly_of_avoiding X m
    intro B hB
    have hBA : B = A := by simpa using hB
    rw [hBA, hd, hord, Int.cast_zero]
  · intro C
    rw [ClosedSectionCycle.principalCycle_apply]
    simp only [Finsupp.sum_single_index, mul_zero, zero_mul, mul_one]
    by_cases hx : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier)
    · rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_left hx]
      obtain ⟨S, hS, hout, he⟩ := hlocal C hx
      exact he.trans (Divisor.SumComparison.sum_eq_local_sum X m A C f d hd S hS hout).symm
    · rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right hx]
      symm
      apply Finset.sum_eq_zero
      intro B _
      have hz : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val = 0 :=
        dite_eq_right (fun h => hx h.2)
      change d B * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val = 0
      rw [hz, mul_zero]

theorem intersection_rationally_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (A : X.DimensionCycleSupport 1) (f : X.carrier.functionField) (hf : f ≠ 0)
    (hord : X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = 0)
    (d : X.RationalDimensionCycle 1)
    (hd : ∀ B : X.DimensionCycleSupport 1, d B = (X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) : ℚ))
    (c : X.RationalDimensionCycle 2)
    (hc : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 1 d (Finsupp.single A 1) c) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 2 c 0 := by
  obtain ⟨g, hg, hi⟩ := exists_principal_intersection X m A f hf hord d hd
  have he := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X 1 1 hc hi
  change c - 0 ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 2
  rw [sub_zero, he]
  exact Submodule.subset_span (ClosedSectionCycle.principalCycle_isPrincipalDivisor X 2 A.val
    (by rw [A.property]) g hg)

end Divisor

end

section

/-! The native rational principal divisor of an integral smooth
presentation is exactly an ThomClass principal-divisor generator. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Cycle

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.DivisorRestriction

def cycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (f : X.carrier.functionField) : X.RationalDimensionCycle 1 :=
  CyclePushforward.degreeComponent X 1 (Affine.DivisorNorm.rationalPrincipalDivisor X.carrier f)

theorem cycle_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (f : X.carrier.functionField) (A : X.DimensionCycleSupport 1) :
    cycle X f A = (X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) : ℚ) := by
  rw [cycle, ClosedSectionCycle.degreeComponent_apply]
  rfl

theorem isPrincipal (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (f : X.carrier.functionField) (hf : f ≠ 0) : CycleClass.Thom.IntersectionGeometry.IsPrincipalDivisor X 1 (cycle X f) := by
  let W : IrreducibleCloseds X.carrier :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X.carrier, isClosed_univ⟩
  let C := ZeroComponents.containingComponent X m W
  have he : C.val = W := by
    apply SetLike.coe_injective
    apply Set.Subset.antisymm (Set.subset_univ _)
    exact ZeroComponents.subset_containingComponent X m W
  have hW : X.supportCodimension W = 0 := by
    rw [← he, C.property]
  let : IsOpenImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι W) := Open.Support.inclusion_isOpenImmersion W isOpen_univ
  let g := Divisor.DivisorRestriction.openFieldMap (CycleClass.Geometric.GenericPoint.reducedSupportι W) f
  have hg : g ≠ 0 := (map_ne_zero_iff _ (Divisor.DivisorRestriction.openFieldMap (CycleClass.Geometric.GenericPoint.reducedSupportι W)).hom.injective).mpr hf
  refine ⟨W, by rw [hW], g, hg, ?_⟩
  intro A
  rw [cycle_apply, CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_left (show CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ (W : Set X.carrier) from trivial)]
  rw [Divisor.DivisorRestriction.ord_openImmersion, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]

theorem principal_eq_cycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (d : X.RationalDimensionCycle 1) (hd : CycleClass.Thom.IntersectionGeometry.IsPrincipalDivisor X 1 d) :
    ∃ f : X.carrier.functionField, f ≠ 0 ∧ d = cycle X f := by
  obtain ⟨W, hW, g, hg, hd⟩ := hd
  have hW0 : X.supportCodimension W = 0 := by omega
  have hopen := Open.Support.codimension_zero_isOpen X m ⟨W, hW0⟩
  have htop : (W : Set X.carrier) = Set.univ :=
    (show IsClopen (W : Set X.carrier) from ⟨W.isClosed, hopen⟩).eq_univ W.isIrreducible.nonempty
  let : IsOpenImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι W) := Open.Support.inclusion_isOpenImmersion W hopen
  let f := (Divisor.DivisorRestriction.openFieldIso (CycleClass.Geometric.GenericPoint.reducedSupportι W)).inv g
  have hf : f ≠ 0 := (map_ne_zero_iff _
    (Divisor.DivisorRestriction.openFieldIso (CycleClass.Geometric.GenericPoint.reducedSupportι W)).commRingCatIsoToRingEquiv.symm.injective).mpr hg
  have hfg : Divisor.DivisorRestriction.openFieldMap (CycleClass.Geometric.GenericPoint.reducedSupportι W) f = g :=
    (Divisor.DivisorRestriction.openFieldIso (CycleClass.Geometric.GenericPoint.reducedSupportι W)).commRingCatIsoToRingEquiv.apply_symm_apply g
  refine ⟨f, hf, Finsupp.ext (fun A => ?_)⟩
  have hx : CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ (W : Set X.carrier) := by rw [htop]; trivial
  rw [hd, cycle_apply, CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_left hx, ← hfg,
    Divisor.DivisorRestriction.ord_openImmersion, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]

theorem cycle_mul (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (f g : X.carrier.functionField) (hf : f ≠ 0) (hg : g ≠ 0) :
    cycle X (f * g) = cycle X f + cycle X g := by
  ext A
  rw [Finsupp.add_apply, cycle_apply, cycle_apply, cycle_apply, Scheme.ord_mul hf hg, Int.cast_add]

theorem intersection_rationally_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (A : X.DimensionCycleSupport 1) (f : X.carrier.functionField) (hf : f ≠ 0)
    (hord : X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = 0)
    (c : X.RationalDimensionCycle 2)
    (hc : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 1 (cycle X f) (Finsupp.single A 1) c) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 2 c 0 :=
  Divisor.intersection_rationally_zero X m A f hf hord (cycle X f)
    (cycle_apply X f) c hc

end Cycle

end

/-! On an integral smooth presentation, a rational principal-divisor
relation becomes one actual principal divisor after multiplication by
a positive integer. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Denominator

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Integral.Cycle

theorem cycle_one (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier] :
    Cycle.cycle X 1 = 0 := by
  ext A
  rw [Cycle.cycle_apply, Finsupp.zero_apply]
  have h := DivisorInverse.ord_inv X.carrier 1 (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
  rw [inv_one] at h
  have hz : X.carrier.ord 1 (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = 0 := by omega
  rw [hz, Int.cast_zero]

theorem cycle_inv (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (f : X.carrier.functionField) : Cycle.cycle X f⁻¹ = -Cycle.cycle X f := by
  ext A
  rw [Cycle.cycle_apply, Finsupp.neg_apply, Cycle.cycle_apply, DivisorInverse.ord_inv, Int.cast_neg]

theorem cycle_pow (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (f : X.carrier.functionField) (hf : f ≠ 0) (n : ℕ) :
    Cycle.cycle X (f ^ n) = (n : ℚ) • Cycle.cycle X f := by
  induction n with
  | zero => rw [pow_zero, cycle_one, Nat.cast_zero, zero_smul]
  | succ n ih =>
    rw [pow_succ, Cycle.cycle_mul X _ _ (pow_ne_zero n hf) hf, ih, Nat.cast_add, Nat.cast_one,
      add_smul, one_smul]

theorem cycle_zpow (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (f : X.carrier.functionField) (hf : f ≠ 0) (n : ℤ) :
    Cycle.cycle X (f ^ n) = (n : ℚ) • Cycle.cycle X f := by
  cases n with
  | ofNat n =>
    change Cycle.cycle X (f ^ (n : ℤ)) = (n : ℚ) • Cycle.cycle X f
    rw [zpow_natCast, cycle_pow X f hf]
  | negSucc n =>
    rw [zpow_negSucc, cycle_inv, cycle_pow X f hf]
    simp only [Int.cast_negSucc, neg_smul, Nat.cast_add, Nat.cast_one]

theorem exists_multiple (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (d : X.RationalDimensionCycle 1) (hd : d ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ f : X.carrier.functionField, f ≠ 0 ∧ (n : ℚ) • d = Cycle.cycle X f := by
  induction hd using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨f, hf, rfl⟩ := Cycle.principal_eq_cycle X m d hd
    exact ⟨1, one_ne_zero, f, hf, one_smul ℚ _⟩
  | zero => exact ⟨1, one_ne_zero, 1, one_ne_zero, by rw [smul_zero, cycle_one]⟩
  | add d e _ _ ihd ihe =>
    obtain ⟨n, hn, f, hf, heq⟩ := ihd
    obtain ⟨k, hk, g, hg, heq'⟩ := ihe
    refine ⟨n * k, Nat.mul_ne_zero hn hk, f ^ k * g ^ n,
      mul_ne_zero (pow_ne_zero k hf) (pow_ne_zero n hg), ?_⟩
    rw [Cycle.cycle_mul X _ _ (pow_ne_zero k hf) (pow_ne_zero n hg),
      cycle_pow X f hf, cycle_pow X g hg, ← heq, ← heq', smul_add,
      smul_smul, smul_smul, Nat.cast_mul]
    congr 1
    rw [mul_comm]
  | smul q d _ ih =>
    obtain ⟨n, hn, f, hf, heq⟩ := ih
    refine ⟨n * q.den, Nat.mul_ne_zero hn q.den_nz, f ^ q.num, zpow_ne_zero _ hf, ?_⟩
    rw [cycle_zpow X f hf, ← heq, smul_smul, smul_smul, Nat.cast_mul]
    have hq : q * (q.den : ℚ) = (q.num : ℚ) :=
      (eq_div_iff (Nat.cast_ne_zero.mpr q.den_nz)).mp q.num_div_den.symm
    congr 1
    calc
      (n : ℚ) * q.den * q = n * (q * q.den) := by ring
      _ = q.num * n := by rw [hq, mul_comm]

end Denominator

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Integral
