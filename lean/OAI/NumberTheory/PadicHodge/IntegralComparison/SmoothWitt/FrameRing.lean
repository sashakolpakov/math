import OAI.NumberTheory.PadicHodge.IntegralComparison.FlatWittDividedPowers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation

/-! # Frame Ring -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing

noncomputable section

/-! The original p-power quotients of a smooth flat Witt lift carry compatible divided powers. -/

universe u

variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]

local notation "W" => WittVector p k
local notation "I" => Ideal.span {(p : A)}
local notation "δ" => OAI.NumberTheory.PadicHodge.IntegralComparison.FlatWittDividedPowers.dividedPowers p k A

abbrev Ring (n : ℕ) := AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.Ring A I n

def base (n : ℕ) : W →+* Ring p A n :=
  (Ideal.Quotient.mk (I ^ (n + 1))).comp (algebraMap W A)

def ideal (n : ℕ) : Ideal (Ring p A n) := AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.ideal A I n

def dividedPowers (n : ℕ) : DividedPowers (ideal p A n) :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.dividedPowers A I δ n

omit [Fintype k] in
theorem base_isDPMorphism (n : ℕ) : DividedPowers.IsDPMorphism
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (dividedPowers p k A n) (base p k A n) :=
  (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.quotient_isDPMorphism A I δ n).comp _
    (FlatWittDividedPowers.base_isDPMorphism p k A)

omit [Fact p.Prime] [Field k] [Fintype k] [CharP k p]
  [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A] in
theorem prime_power_zero (n : ℕ) : (p : Ring p A n) ^ (n + 1) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (I ^ (n + 1))) p, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton (p : A))) (n + 1))

variable (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) = algebraMap k C (WittVector.constantCoeff w))

def reduction (n : ℕ) : Ring p A n →+* C :=
  AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.reduction A I ρ hker n

def quotientEquiv (n : ℕ) : (Ring p A n ⧸ ideal p A n) ≃+* C :=
  (Ideal.quotEquivOfEq (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.reduction_kernel A I ρ hker n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.reduction_surjective A I ρ hker hρ n))

omit [Fact p.Prime] in
theorem quotientEquiv_mk (n : ℕ) (a : Ring p A n) :
    quotientEquiv p A C ρ hρ hker n (Ideal.Quotient.mk (ideal p A n) a) = reduction p A C ρ hker n a := by
  change (RingHom.quotientKerEquivOfSurjective
    (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.reduction_surjective A I ρ hker hρ n))
      ((Ideal.quotEquivOfEq (AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation.reduction_kernel A I ρ hker n).symm)
        (Ideal.Quotient.mk _ a)) = _
  rw [Ideal.quotEquivOfEq_mk]
  rfl

omit [Fintype k] [CharP k p] [Module.Flat (WittVector p k) A] in
include hbase in
theorem quotientEquiv_base (n : ℕ) (w : W) :
    quotientEquiv p A C ρ hρ hker n (Ideal.Quotient.mk (ideal p A n) (base p k A n w)) =
      algebraMap k C (WittVector.constantCoeff w) := by
  rw [quotientEquiv_mk]
  exact hbase w

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing
