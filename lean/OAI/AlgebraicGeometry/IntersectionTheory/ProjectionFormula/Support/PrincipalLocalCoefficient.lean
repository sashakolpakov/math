import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.SupportMultiplicity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeRatioOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.PrincipalLeft

/-! # Principal Local Coefficient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.PrincipalLocalCoefficient

noncomputable section

section

/-! Principal support-cycle coefficients and their divisor intersection
multiplicities are the two factors in local surface reciprocity. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CanonicalSurfaceReciprocity

theorem principal (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (x : X.carrier) (hxW : x ∈ (W.val : Set X.carrier))
    (p : PrimeSpectrum ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)))
    (hp : p.asIdeal.height = 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField)
    (a b : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW))
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : g = algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW))
        (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField a /
      algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW))
        (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField b) :
    Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g
      ⟨LocalDivisor.support X k W x hxW p, LocalDivisor.codimension X k W x hxW p m hp⟩ =
        CanonicalSurfaceReciprocity.weight ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)) p a -
        CanonicalSurfaceReciprocity.weight ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)) p b := by
  let A := LocalDivisor.support X k W x hxW p
  have hAW : CycleClass.Thom.IntersectionGeometry.supportPoint A ∈ (W.val : Set X.carrier) :=
    LocalDivisor.subset X k W x hxW p (A.isIrreducible.isGenericPoint_genericPoint A.isClosed).mem
  have hy : CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint A) hAW =
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW) p := by
    apply (CycleClass.Geometric.GenericPoint.reducedSupportι W.val).isEmbedding.injective
    rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]
    exact LocalDivisor.support_point X k W x hxW p
  rw [Principal.ClosedSectionCycle.principalCycle_apply, CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_left hAW, hy, hab]
  exact Stalk.PrimeRatioOrder.ambient (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val) (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW) p hp a b ha hb

theorem multiplicity (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
    (D : X.DimensionCycleSupport 1) (W : X.DimensionCycleSupport k) (C : X.DimensionCycleSupport (k + 2))
    (hxD : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (D.val : Set X.carrier))
    (hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W.val : Set X.carrier))
    (r : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) (hr : r ≠ 0)
    (he : RingHom.ker (Local.Principal.supportStalkMap X.carrier D.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxD).hom = Ideal.span {r})
    (p : PrimeSpectrum ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
      (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW)))
    (hfp : Local.Principal.supportStalkMap X.carrier W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW r ∉ p.asIdeal) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val (LocalDivisor.support X k W (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW p) C.val =
      CanonicalSurfaceReciprocity.restrictedOrder ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
        (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW)) p
        (Local.Principal.supportStalkMap X.carrier W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW r) := by
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
  let A := LocalDivisor.support X k W x hxW p
  let hAW := LocalDivisor.subset X k W x hxW p
  let hxA := LocalDivisor.point_mem X k W x hxW p
  let f := Local.Principal.supportStalkMap X.carrier W.val x hxW r
  let τ := NestedSupportStalk.stalkMap X.carrier A W.val hAW x hxA hxW
  have hk : RingHom.ker τ.hom = p.asIdeal := LocalDivisor.kernel_eq X k W x hxW p
  have hτ : τ f ≠ 0 := fun hz => hfp (hk ▸ RingHom.mem_ker.mpr hz)
  have hcomp : τ f = Local.Principal.supportStalkMap X.carrier A x hxA r :=
    NestedSupportStalk.apply_comp X.carrier A W.val hAW x hxA hxW r
  have hra : Local.Principal.supportStalkMap X.carrier A x hxA r ≠ 0 := hcomp ▸ hτ
  have hord := NestedSupportPrime.order X.carrier A W.val hAW x hxA hxW f
  change Ring.ord _ (τ f) = _ at hord
  rw [hk, hcomp] at hord
  exact (Local.PrincipalLeft.intersectionMultiplicity_eq_order X A D.val C.val hxA hxD r hr he hra).trans
    (congrArg (fun n : ℕ∞ => (n.toNat : ℚ)) hord)

end

/-! Reindex intersection with an actual support principal divisor by
the finite union of the numerator and denominator primes in its stalk. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Sum

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CanonicalSurfaceReciprocity

theorem coefficient (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (D : X.DimensionCycleSupport 1) (W : X.DimensionCycleSupport k) (C : X.DimensionCycleSupport (k + 2))
    (hxD : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (D.val : Set X.carrier))
    (hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W.val : Set X.carrier))
    (r : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) (hr : r ≠ 0)
    (he : RingHom.ker (Local.Principal.supportStalkMap X.carrier D.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxD).hom = Ideal.span {r})
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField)
    (a b : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
      (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW)) (ha : a ≠ 0) (hb : b ≠ 0)
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
    (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g).sum
      (fun A c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val A.val C.val) =
      ∑ p ∈ CanonicalSurfaceReciprocity.primes R a ha ∪ CanonicalSurfaceReciprocity.primes R b hb,
        (CanonicalSurfaceReciprocity.weight R p a - CanonicalSurfaceReciprocity.weight R p b) * CanonicalSurfaceReciprocity.restrictedOrder R p f := by
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
  let R := (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)
  let f := Local.Principal.supportStalkMap X.carrier W.val x hxW r
  let S := CanonicalSurfaceReciprocity.primes R a ha ∪ CanonicalSurfaceReciprocity.primes R b hb
  let d := Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g
  let A (p : PrimeSpectrum R) (hp : p.asIdeal.height = 1) : X.DimensionCycleSupport (k + 1) :=
    ⟨LocalDivisor.support X k W x hxW p, LocalDivisor.codimension X k W x hxW p m hp⟩
  have hS (p : PrimeSpectrum R) (hp : p ∈ S) : p.asIdeal.height = 1 := by
    rcases Finset.mem_union.mp hp with h | h
    · exact ((CanonicalSurfaceReciprocity.mem_primes R a ha p).mp h).1
    · exact ((CanonicalSurfaceReciprocity.mem_primes R b hb p).mp h).1
  have hfp (p : PrimeSpectrum R) (hp : p ∈ S) : f ∉ p.asIdeal := by
    intro h
    rcases Finset.mem_union.mp hp with hpa | hpb
    · exact (havoid p (hS p hp) h).1 ((CanonicalSurfaceReciprocity.mem_primes R a ha p).mp hpa).2
    · exact (havoid p (hS p hp) h).2 ((CanonicalSurfaceReciprocity.mem_primes R b hb p).mp hpb).2
  have hd (p : PrimeSpectrum R) (hp : p.asIdeal.height = 1) :
      d (A p hp) = CanonicalSurfaceReciprocity.weight R p a - CanonicalSurfaceReciprocity.weight R p b :=
    principal X m k W x hxW p hp g a b ha hb hab
  have hi (p : PrimeSpectrum R) (hp : p ∈ S) :
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val (A p (hS p hp)).val C.val = CanonicalSurfaceReciprocity.restrictedOrder R p f :=
    multiplicity X k D W C hxD hxW r hr he p (hfp p hp)
  have hterm (p : PrimeSpectrum R) (hp : p ∈ S) :
      (CanonicalSurfaceReciprocity.weight R p a - CanonicalSurfaceReciprocity.weight R p b) * CanonicalSurfaceReciprocity.restrictedOrder R p f =
        d (A p (hS p hp)) * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val (A p (hS p hp)).val C.val := by
    rw [hd p (hS p hp), hi p hp]
  change d.sum (fun B c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X D.val B.val C.val) =
    ∑ p ∈ S, (CanonicalSurfaceReciprocity.weight R p a - CanonicalSurfaceReciprocity.weight R p b) * CanonicalSurfaceReciprocity.restrictedOrder R p f
  symm
  apply Finset.sum_bij_ne_zero (fun p hp _ => A p (hS p hp))
  · intro p hp hn
    exact Finsupp.mem_support_iff.mpr (mul_ne_zero_iff.mp ((hterm p hp) ▸ hn)).1
  · intro p hp _ q hq _ heq
    apply DivisorPrime.support_injective X k W x hxW
    exact congrArg Subtype.val heq
  · intro B hB hn
    have hxB : x ∈ (B.val : Set X.carrier) := by
      by_contra h
      exact (mul_ne_zero_iff.mp hn).2 (dite_eq_right (fun hm => h hm.2))
    have hBWpoint : CycleClass.Thom.IntersectionGeometry.supportPoint B.val ∈ (W.val : Set X.carrier) := by
      by_contra h
      have hz : d B = 0 := by
        rw [Principal.ClosedSectionCycle.principalCycle_apply, CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right h]
      exact Finsupp.mem_support_iff.mp hB hz
    have hBW : B.val ≤ W.val :=
      (Supports.supportPoint_mem_iff_subset
        (⟨(W.val : Set X.carrier), W.val.isClosed⟩ : Closeds X.carrier) B.val).mp hBWpoint
    let p := DivisorPrime.prime X k W x hxW B.val hBW hxB
    have hp : p.asIdeal.height = 1 := DivisorPrime.height X k W x hxW m B hBW hxB
    have him : A p hp = B := Subtype.ext (DivisorPrime.image X k W x hxW B.val hBW hxB)
    have hcoeff : d B = CanonicalSurfaceReciprocity.weight R p a - CanonicalSurfaceReciprocity.weight R p b := by
      rw [← him]
      exact hd p hp
    have hpS : p ∈ S := by
      by_contra hout
      have hpa : p ∉ CanonicalSurfaceReciprocity.primes R a ha := fun h => hout (Finset.mem_union_left _ h)
      have hpb : p ∉ CanonicalSurfaceReciprocity.primes R b hb := fun h => hout (Finset.mem_union_right _ h)
      have hz : d B = 0 := hcoeff.trans (by
        rw [CanonicalSurfaceReciprocity.weight_eq_zero R a ha p hp hpa, CanonicalSurfaceReciprocity.weight_eq_zero R b hb p hp hpb, sub_self])
      exact Finsupp.mem_support_iff.mp hB hz
    have hn' : (CanonicalSurfaceReciprocity.weight R p a - CanonicalSurfaceReciprocity.weight R p b) * CanonicalSurfaceReciprocity.restrictedOrder R p f ≠ 0 := by
      rw [hterm p hpS, him]
      exact hn
    exact ⟨p, hpS, hn', him⟩
  · intro p hp _
    exact hterm p hp

end Sum

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.PrincipalLocalCoefficient
