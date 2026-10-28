import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.WittPermutation
import OAI.NumberTheory.PadicHodge.IntegralComparison.PermutationPolynomial

/-! # Witt Polynomial -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.WittPolynomial

noncomputable section

/-! The original Witt action of a finite étale algebra automorphism has an integral permutation polynomial. -/

open scoped TensorProduct

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

universe u

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [CommRing A] [Algebra k A]
  [CharP k p] [PerfectRing k p] [Nontrivial A] [Module.Finite k A] [Algebra.Etale k A]

local notation "Ω" => AlgebraicClosure k
local notation "T" => Ω ⊗[k] A

local instance : Fintype (PrimeSpectrum T) :=
  let := WittSplitting.finite_index k A
  Fintype.ofFinite _
local instance : DecidableEq (PrimeSpectrum T) := Classical.decEq _
local instance : Module.Free (WittVector p k) (WittVector p A) := PeriodInvariants.FiniteEtaleWittModule.free p k A
local instance : Module.Finite (WittVector p k) (WittVector p A) := PeriodInvariants.FiniteEtaleWittModule.finite p k A

omit p [Fact p.Prime] [CharP k p] [PerfectRing k p] [Nontrivial A] [Algebra.Etale k A] in
def polynomial (e : A ≃ₐ[k] A) : Polynomial ℤ :=
  PermutationPolynomial.Characteristic.polynomial (WittPermutation.permutation k A e)

omit p [Fact p.Prime] [CharP k p] [PerfectRing k p] [Nontrivial A] [Algebra.Etale k A] in
theorem monic (e : A ≃ₐ[k] A) : (polynomial k A e).Monic :=
  PermutationPolynomial.Characteristic.monic _

theorem conjugate (e : A ≃ₐ[k] A) :
    (WittSplitting.equiv p k A).toLinearEquiv.conj
      ((PeriodInvariants.WittAlgebraFunctor.map p k e.toAlgHom).toLinearMap.baseChange (WittVector p Ω)) =
        PermutationPolynomial.Ring.action (WittPermutation.permutation k A e) (WittVector p Ω) := by
  apply LinearMap.ext
  intro f
  funext i
  change WittSplitting.equiv p k A
    ((PeriodInvariants.WittAlgebraFunctor.map p k e.toAlgHom).toLinearMap.baseChange (WittVector p Ω)
      ((WittSplitting.equiv p k A).symm f)) i =
        f (WittPermutation.permutation k A e i)
  rw [WittPermutation.action, AlgEquiv.apply_symm_apply]

theorem split_charpoly (e : A ≃ₐ[k] A) :
    ((PeriodInvariants.WittAlgebraFunctor.map p k e.toAlgHom).toLinearMap.baseChange (WittVector p Ω)).charpoly =
      (polynomial k A e).map (Int.castRingHom (WittVector p Ω)) := by
  rw [← (WittSplitting.equiv p k A).toLinearEquiv.charpoly_conj, conjugate,
    PermutationPolynomial.Ring.charpoly]
  rfl

theorem integral (e : A ≃ₐ[k] A) :
    (PeriodInvariants.WittAlgebraFunctor.map p k e.toAlgHom).toLinearMap.charpoly =
      (polynomial k A e).map (Int.castRingHom (WittVector p k)) := by
  apply Polynomial.map_injective (algebraMap (WittVector p k) (WittVector p Ω))
    (WittVector.map_injective (algebraMap k Ω) (algebraMap k Ω).injective)
  rw [← LinearMap.charpoly_baseChange, split_charpoly, Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

theorem rational (e : A ≃ₐ[k] A) :
    ((PeriodInvariants.WittAlgebraFunctor.map p k e.toAlgHom).toLinearMap.baseChange (FractionRing (WittVector p k))).charpoly =
      (polynomial k A e).map (Int.castRingHom (FractionRing (WittVector p k))) := by
  rw [LinearMap.charpoly_baseChange, integral, Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.WittPolynomial
