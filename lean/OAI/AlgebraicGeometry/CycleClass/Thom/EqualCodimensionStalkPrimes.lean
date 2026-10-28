import OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports

/-! # Equal Codimension Stalk Primes -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EqualCodimensionStalkPrimes.Constructions

noncomputable section

/-! At a common point, distinct integral supports of one codimension
give incomparable primes in the actual ambient stalk. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem support_le_of_kernel_le (X : Scheme) (A B : IrreducibleCloseds X) (x : X)
    (hxA : x ∈ (A : Set X)) (hxB : x ∈ (B : Set X))
    (h : (StalkPrimeQuotient.Constructions.kernelPrime X A x hxA).asIdeal ≤ (StalkPrimeQuotient.Constructions.kernelPrime X B x hxB).asIdeal) : B ≤ A := by
  have hs := (PrimeSpectrum.le_iff_specializes (StalkPrimeQuotient.Constructions.kernelPrime X A x hxA) (StalkPrimeQuotient.Constructions.kernelPrime X B x hxB)).mp h
  have ht := Scheme.le_iff_specializes.mpr (hs.map (X.fromSpecStalk x).continuous)
  rw [StalkPrimeQuotient.Constructions.kernelPrime_image, StalkPrimeQuotient.Constructions.kernelPrime_image] at ht
  exact irreducibleSetEquivPoints.le_iff_le.mp ht

theorem support_eq_of_kernel_le (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (A B : X.DimensionCycleSupport p) (x : X.carrier)
    (hxA : x ∈ (A.val : Set X.carrier)) (hxB : x ∈ (B.val : Set X.carrier))
    (h : (StalkPrimeQuotient.Constructions.kernelPrime X.carrier A.val x hxA).asIdeal ≤ (StalkPrimeQuotient.Constructions.kernelPrime X.carrier B.val x hxB).asIdeal) : A = B := by
  have hBA := support_le_of_kernel_le X.carrier A.val B.val x hxA hxB h
  apply Subtype.ext
  by_contra hn
  have hl := Intersection.Supports.codimension_strictAnti X (lt_of_le_of_ne hBA (Ne.symm hn))
  rw [A.property, B.property] at hl
  exact Nat.lt_irrefl p hl

theorem kernel_antichain (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (A B : X.DimensionCycleSupport p) (x : X.carrier)
    (hxA : x ∈ (A.val : Set X.carrier)) (hxB : x ∈ (B.val : Set X.carrier))
    (h : (StalkPrimeQuotient.Constructions.kernelPrime X.carrier A.val x hxA).asIdeal ≤ (StalkPrimeQuotient.Constructions.kernelPrime X.carrier B.val x hxB).asIdeal) :
    (StalkPrimeQuotient.Constructions.kernelPrime X.carrier A.val x hxA).asIdeal = (StalkPrimeQuotient.Constructions.kernelPrime X.carrier B.val x hxB).asIdeal := by
  obtain rfl := support_eq_of_kernel_le X p A B x hxA hxB h
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EqualCodimensionStalkPrimes.Constructions
