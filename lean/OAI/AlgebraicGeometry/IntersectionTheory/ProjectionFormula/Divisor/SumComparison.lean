import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RestrictedDivisorOrder

/-! # Sum Comparison -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.SumComparison

noncomputable section

/-! Reindex the local prime sum by the actual finite dimension-graded
divisor cycle. Terms outside the stalk's spectrum have zero multiplicity. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem sum_eq_local_sum (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (A : X.DimensionCycleSupport 1) (C : X.DimensionCycleSupport 2)
    (f : X.carrier.functionField) (d : X.RationalDimensionCycle 1)
    (hd : ∀ B : X.DimensionCycleSupport 1, d B = (X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) : ℚ))
    (S : Finset (Spec (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))))
    (hS : ∀ p ∈ S, p.asIdeal.height = 1 ∧
      X.supportCodimension (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) = 1)
    (hout : ∀ p : Spec (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)),
      p.asIdeal.height = 1 → p ∉ S →
        X.carrier.ord f (X.carrier.fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) = 0) :
    d.sum (fun B c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val) =
      ∑ p ∈ S, (X.carrier.ord f (X.carrier.fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) : ℚ) *
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) A.val C.val := by
  symm
  let B (p : Spec (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))) (hp : p ∈ S) :
      X.DimensionCycleSupport 1 :=
    ⟨Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p, (hS p hp).2⟩
  have hterm (p : Spec (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))) (hp : p ∈ S) :
      (X.carrier.ord f (X.carrier.fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) : ℚ) *
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) A.val C.val =
      d (B p hp) * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (B p hp).val A.val C.val := by
    rw [hd, Stalk.DivisorSupport.primeClosure_point]
  apply Finset.sum_bij_ne_zero (fun p hp _ => B p hp)
  · intro p hp hn
    apply Finsupp.mem_support_iff.mpr
    exact (mul_ne_zero_iff.mp ((hterm p hp) ▸ hn)).1
  · intro p hp _ q hq _ he
    apply (X.carrier.fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)).isEmbedding.injective
    have he' := congrArg (fun D : X.DimensionCycleSupport 1 => CycleClass.Thom.IntersectionGeometry.supportPoint D.val) he
    simpa only [B, Stalk.DivisorSupport.primeClosure_point] using he'
  · intro D hD hn
    have hχ : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A.val C.val ≠ 0 := (mul_ne_zero_iff.mp hn).2
    have hxD : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (D.val : Set X.carrier) := by
      by_contra h
      exact hχ (dite_eq_right (fun hm => h hm.1))
    have hspecial : CycleClass.Thom.IntersectionGeometry.supportPoint D.val ⤳ CycleClass.Thom.IntersectionGeometry.supportPoint C.val :=
      (D.val.isIrreducible.isGenericPoint_genericPoint D.val.isClosed).specializes hxD
    have hrange : CycleClass.Thom.IntersectionGeometry.supportPoint D.val ∈ Set.range (X.carrier.fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) := by
      rw [Scheme.range_fromSpecStalk]
      exact hspecial
    obtain ⟨p, hpD⟩ := hrange
    have hp : p.asIdeal.height = 1 := by
      rw [Stalk.Localization.height_eq_coheight_image, hpD]
      exact CurveSupports.coheight_one X m D
    have hpS : p ∈ S := by
      by_contra h
      have ho := hout p hp h
      rw [hpD] at ho
      have hd0 := hd D
      rw [ho, Int.cast_zero] at hd0
      exact Finsupp.mem_support_iff.mp hD hd0
    have he : B p hpS = D := by
      apply Subtype.ext
      apply irreducibleSetEquivPoints.injective
      exact (Stalk.DivisorSupport.primeClosure_point X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p).trans hpD
    have hn' := hn
    change d D * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A.val C.val ≠ 0 at hn'
    rw [← he, ← hterm p hpS] at hn'
    exact ⟨p, hpS, hn', he⟩
  · intro p hp _
    exact hterm p hp

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.SumComparison
