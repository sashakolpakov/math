import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Order
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ResidueDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.Ord

/-! # Divisor Norm -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

noncomputable section

/-! Proper pushforward of the actual principal divisor for a finite normal
affine scheme over a DVR. Coefficients are scheme orders and native scheme
residue degrees; the norm uses the canonical function-field isomorphisms. -/

set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry IsDedekindDomain _root_.Order
open scoped Classical BigOperators

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Order OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

universe u

def rationalPrincipalDivisor (X : Scheme.{u}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (f : X.functionField) : X →₀ ℚ :=
  (Divisors.LineBundles.Ord.BundleCycles.principalDivisor X f).mapRange (fun n : ℤ => (n : ℚ)) (by simp)

@[simp]
theorem rationalPrincipalDivisor_apply (X : Scheme.{u}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (f : X.functionField) (x : X) :
    rationalPrincipalDivisor X f x = (X.ord f x : ℚ) := rfl

variable (S : Type u) [CommRing S] [IsDedekindDomain S]

omit [IsDedekindDomain S] in
theorem branchPoint_injective : Function.Injective (Order.branchPoint S) := by
  intro P Q h
  exact HeightOneSpectrum.ext (congrArg PrimeSpectrum.asIdeal h)

theorem rationalPrincipalDivisor_eq_sum [Fintype (HeightOneSpectrum S)]
    (f : (Spec (.of S)).functionField) :
    rationalPrincipalDivisor (Spec (.of S)) f =
      ∑ P : HeightOneSpectrum S, Finsupp.single (Order.branchPoint S P)
        ((Spec (.of S)).ord f (Order.branchPoint S P) : ℚ) := by
  ext x
  rw [rationalPrincipalDivisor_apply, Finsupp.finsetSum_apply]
  by_cases hx : x.asIdeal = ⊥
  · have hc : coheight x ≠ 1 := by
      rw [← idealHeight_eq_coheight, hx, Ideal.height_bot]
      decide
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hc, Int.cast_zero]
    symm
    apply Finset.sum_eq_zero
    intro P _
    apply Finsupp.single_eq_of_ne
    intro h
    exact P.ne_bot ((congrArg PrimeSpectrum.asIdeal h.symm).trans hx)
  · let P : HeightOneSpectrum S := ⟨x.asIdeal, x.isPrime, hx⟩
    have he : Order.branchPoint S P = x := rfl
    rw [← he]
    rw [Finset.sum_eq_single P]
    · exact (Finsupp.single_eq_same).symm
    · intro Q _ hQP
      exact Finsupp.single_eq_of_ne (fun h => hQP (branchPoint_injective S h.symm))
    · simp

theorem rationalPrincipalDivisor_local [IsDiscreteValuationRing S]
    (f : (Spec (.of S)).functionField) :
    rationalPrincipalDivisor (Spec (.of S)) f =
      Finsupp.single (Order.branchPoint S (Order.closedBranch S))
        ((Spec (.of S)).ord f (Order.branchPoint S (Order.closedBranch S)) : ℚ) := by
  ext x
  rw [rationalPrincipalDivisor_apply]
  by_cases hx : x.asIdeal = ⊥
  · have hc : coheight x ≠ 1 := by
      rw [← idealHeight_eq_coheight, hx, Ideal.height_bot]
      decide
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hc, Int.cast_zero]
    symm
    apply Finsupp.single_eq_of_ne
    intro h
    exact (Order.closedBranch S).ne_bot ((congrArg PrimeSpectrum.asIdeal h.symm).trans hx)
  · have he : x = Order.branchPoint S (Order.closedBranch S) := by
      apply PrimeSpectrum.ext
      exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal x.isPrime hx)
    rw [he, Finsupp.single_eq_same]

theorem affineMap_branchPoint_local (R : Type u) [CommRing R] [IsLocalRing R]
    [Algebra R S] [Module.Finite R S] (P : HeightOneSpectrum S) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Order.branchPoint S P) =
      (IsLocalRing.closedPoint R : Spec (.of R)) := by
  apply PrimeSpectrum.ext
  exact IsLocalRing.eq_maximalIdeal (inferInstanceAs (P.asIdeal.under R).IsMaximal)

theorem pushforward_rationalPrincipalDivisor_local (R : Type u)
    [CommRing R] [IsLocalRing R] [Algebra R S] [Module.Finite R S]
    [Fintype (HeightOneSpectrum S)] (f : (Spec (.of S)).functionField) :
    CyclePushforward.pointPushforward (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (rationalPrincipalDivisor (Spec (.of S)) f) =
        Finsupp.single (IsLocalRing.closedPoint R : Spec (.of R))
          (∑ P : HeightOneSpectrum S, (P.asIdeal.inertiaDeg R : ℚ) *
            ((Spec (.of S)).ord f (Order.branchPoint S P) : ℚ)) := by
  rw [rationalPrincipalDivisor_eq_sum, map_sum, Finsupp.single_finsetSum]
  apply Finset.sum_congr rfl
  intro P _
  rw [CyclePushforward.pointPushforward_single, affineMap_branchPoint_local,
    ResidueDegree.residueDegree_eq_inertiaDeg]
  congr 1
  exact mul_comm _ _

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R S] [Module.Finite R S]

theorem affineMap_branchPoint (P : HeightOneSpectrum S) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Order.branchPoint S P) =
      Order.branchPoint R (Order.closedBranch R) := affineMap_branchPoint_local S R P

theorem pushforward_rationalPrincipalDivisor [Fintype (HeightOneSpectrum S)]
    (f : (Spec (.of S)).functionField) :
    CyclePushforward.pointPushforward (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (rationalPrincipalDivisor (Spec (.of S)) f) =
        Finsupp.single (Order.branchPoint R (Order.closedBranch R))
          (∑ P : HeightOneSpectrum S, ((P.asIdeal.inertiaDeg R : ℕ) : ℚ) *
            ((Spec (.of S)).ord f (Order.branchPoint S P) : ℚ)) :=
  pushforward_rationalPrincipalDivisor_local S R f

attribute [local instance] FractionRing.liftAlgebra

/-- Finite affine norm-divisor identity, with all branches and poles. -/
theorem principalDivisor_norm [Module.IsTorsionFree R S]
    [PerfectField (FractionRing R)] (f : FractionRing S) (hf : f ≠ 0) :
    CyclePushforward.pointPushforward (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (rationalPrincipalDivisor (Spec (.of S)) (Order.affineFunctionFieldIso S f)) =
        rationalPrincipalDivisor (Spec (.of R))
          (Order.affineFunctionFieldIso R (Algebra.norm (FractionRing R) f)) := by
  let : Finite (HeightOneSpectrum S) := BranchOrder.finite_heightOneSpectrum R S
  let := Fintype.ofFinite (HeightOneSpectrum S)
  rw [pushforward_rationalPrincipalDivisor, rationalPrincipalDivisor_local,
    Order.schemeOrder_closed, SemilocalDivisorNorm.log_ordFrac_norm R f hf]
  congr 1
  simp_rw [Order.schemeOrder_eq_localOrder]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm
