import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RestrictedSupportCoefficient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SupportMultiplicity

/-! # Restricted Support Sum -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RestrictedSupportSum

noncomputable section

/-! Reindex the constructed principal relation by all height-one
components of the divisor equation in the actual support stalk. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CanonicalSurfaceReciprocity

theorem coefficient (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (D : X.DimensionCycleSupport 1) (W : X.DimensionCycleSupport k) (hDW : ¬ W.val ≤ D.val)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField)
    (hunit : ∀ y : CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val, Order.coheight y = 1 →
      CycleClass.Geometric.GenericPoint.reducedSupportι W.val y ∈ (D.val : Set X.carrier) →
        ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y, IsUnit u ∧
          algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk y)
            (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField u = g)
    (C : X.DimensionCycleSupport (1 + (k + 1)))
    (hxD : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (D.val : Set X.carrier))
    (hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W.val : Set X.carrier))
    (r : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) (hr : r ≠ 0)
    (he : RingHom.ker (Local.Principal.supportStalkMap X.carrier D.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxD).hom = Ideal.span {r})
    (a b : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
      (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW))
    (havoid : ∀ p : PrimeSpectrum ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
        (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW)), p.asIdeal.height = 1 →
      Local.Principal.supportStalkMap X.carrier W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW r ∈ p.asIdeal →
        a ∉ p.asIdeal ∧ b ∉ p.asIdeal)
    (hab : g = algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
        (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW)) (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField a /
      algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
        (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW)) (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField b) :
    let R := (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW)
    let f := Local.Principal.supportStalkMap X.carrier W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW r
    let hf := Local.SupportMultiplicity.restricted_nonzero X k D W hDW _ hxD hxW r he
    RestrictedSupportRelation.cycle X m k D W hDW g hunit C =
      ∑ p ∈ CanonicalSurfaceReciprocity.primes R f hf, CanonicalSurfaceReciprocity.weight R p f * (CanonicalSurfaceReciprocity.restrictedOrder R p a - CanonicalSurfaceReciprocity.restrictedOrder R p b) := by
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
  let R := (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)
  let f := Local.Principal.supportStalkMap X.carrier W.val x hxW r
  have hf : f ≠ 0 := Local.SupportMultiplicity.restricted_nonzero X k D W hDW x hxD hxW r he
  let S := CanonicalSurfaceReciprocity.primes R f hf
  let c := Divisor.SupportCycle.cycle X m k D W
  let A (p : PrimeSpectrum R) (hp : p ∈ S) : c.support :=
    ⟨⟨Support.LocalDivisor.support X k W x hxW p,
      by rw [Support.LocalDivisor.codimension X k W x hxW p m ((CanonicalSurfaceReciprocity.mem_primes R f hf p).mp hp).1]; omega⟩,
      Local.SupportMultiplicity.mem_cycle X m k D W hDW x hxD hxW r hr he p
        ((CanonicalSurfaceReciprocity.mem_primes R f hf p).mp hp).1 ((CanonicalSurfaceReciprocity.mem_primes R f hf p).mp hp).2⟩
  have hweight (p : PrimeSpectrum R) (hp : p ∈ S) : c (A p hp).val = CanonicalSurfaceReciprocity.weight R p f :=
    (Divisor.SupportCycle.coefficient X m k D W hDW (A p hp).val).trans
      (Local.SupportMultiplicity.multiplicity_eq_weight X m k D W hDW x hxD hxW r hr he p
        ((CanonicalSurfaceReciprocity.mem_primes R f hf p).mp hp).1)
  have hterm (p : PrimeSpectrum R) (hp : p ∈ S) :
      RestrictedSupportRelation.term X m k D W hDW g hunit (A p hp).val (A p hp).property C =
        CanonicalSurfaceReciprocity.restrictedOrder R p a - CanonicalSurfaceReciprocity.restrictedOrder R p b := by
    have hxA : x ∈ ((A p hp).val.val : Set X.carrier) := Support.LocalDivisor.point_mem X k W x hxW p
    let hAW := (Divisor.SupportCycle.support_subset X m k D W hDW (A p hp).val (A p hp).property).2
    have hprime : Support.DivisorPrime.prime X k W x hxW (A p hp).val.val hAW hxA = p := by
      apply Support.DivisorPrime.support_injective X k W x hxW
      exact Support.DivisorPrime.image X k W x hxW (A p hp).val.val hAW hxA
    have ha := (havoid p ((CanonicalSurfaceReciprocity.mem_primes R f hf p).mp hp).1 ((CanonicalSurfaceReciprocity.mem_primes R f hf p).mp hp).2).1
    have hb := (havoid p ((CanonicalSurfaceReciprocity.mem_primes R f hf p).mp hp).1 ((CanonicalSurfaceReciprocity.mem_primes R f hf p).mp hp).2).2
    have ha' : a ∉ (Support.DivisorPrime.prime X k W x hxW (A p hp).val.val hAW hxA).asIdeal := by
      rw [hprime]
      exact ha
    have hb' : b ∉ (Support.DivisorPrime.prime X k W x hxW (A p hp).val.val hAW hxA).asIdeal := by
      rw [hprime]
      exact hb
    have h := RestrictedSupportCoefficient.coefficient X m k D W hDW g hunit
      (A p hp).val (A p hp).property C hxW hxA a b ha' hb' hab
    change _ = CanonicalSurfaceReciprocity.restrictedOrder R (Support.DivisorPrime.prime X k W x hxW (A p hp).val.val hAW hxA) a -
      CanonicalSurfaceReciprocity.restrictedOrder R (Support.DivisorPrime.prime X k W x hxW (A p hp).val.val hAW hxA) b at h
    rw [hprime] at h
    exact h
  change (∑ B : c.support, c B.val •
    RestrictedSupportRelation.term X m k D W hDW g hunit B.val B.property) C = _
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  symm
  apply Finset.sum_bij_ne_zero (fun p hp _ => A p hp)
  · intro p hp hn
    exact Finset.mem_univ _
  · intro p hp _ q hq _ heq
    apply Support.DivisorPrime.support_injective X k W x hxW
    exact congrArg (fun B : c.support => B.val.val) heq
  · intro B _ hn
    have hxB : x ∈ (B.val.val : Set X.carrier) := by
      by_contra h
      have hz := RestrictedSupportCoefficient.zero_outside X m k D W hDW g hunit
        B.val B.property C hxW h
      exact hn (by rw [hz, mul_zero])
    let hBW := (Divisor.SupportCycle.support_subset X m k D W hDW B.val B.property).2
    let p := Support.DivisorPrime.prime X k W x hxW B.val.val hBW hxB
    have hp : p.asIdeal.height = 1 := by
      let B' : X.DimensionCycleSupport (k + 1) := ⟨B.val.val, by rw [B.val.property]; omega⟩
      exact Support.DivisorPrime.height X k W x hxW m B' hBW hxB
    have him : Support.LocalDivisor.support X k W x hxW p = B.val.val :=
      Support.DivisorPrime.image X k W x hxW B.val.val hBW hxB
    have hcw : c B.val = CanonicalSurfaceReciprocity.weight R p f := by
      have hi := Local.SupportMultiplicity.multiplicity_eq_weight X m k D W hDW x hxD hxW r hr he p hp
      rw [him] at hi
      exact (Divisor.SupportCycle.coefficient X m k D W hDW B.val).trans hi
    have hpS : p ∈ S := by
      by_contra hout
      have hz := CanonicalSurfaceReciprocity.weight_eq_zero R f hf p hp hout
      exact Finsupp.mem_support_iff.mp B.property (hcw.trans hz)
    have heq : A p hpS = B := Subtype.ext (Subtype.ext him)
    have hn' : CanonicalSurfaceReciprocity.weight R p f * (CanonicalSurfaceReciprocity.restrictedOrder R p a - CanonicalSurfaceReciprocity.restrictedOrder R p b) ≠ 0 := by
      rw [← hweight p hpS, ← hterm p hpS, heq]
      exact hn
    exact ⟨p, hpS, hn', heq⟩
  · intro p hp _
    rw [hweight p hp, hterm p hp]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RestrictedSupportSum
