import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.WittPermutation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry

/-! # Frobenius Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FrobeniusAlgebra

noncomputable section

/-! Relative q-Frobenius and scalar geometric Frobenius induce the same map on geometric prime ideals. -/

open scoped TensorProduct

universe u

variable (k A : Type u) [Field k] [CommRing A] [Algebra k A]

local notation "Ω" => AlgebraicClosure k
local notation "T" => Ω ⊗[k] A

def scalarMap (σ : Ω ≃ₐ[k] Ω) : T →ₐ[k] T :=
  Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k A)

theorem scalarMap_tmul (σ : Ω ≃ₐ[k] Ω) (s : Ω) (a : A) :
    scalarMap k A σ (s ⊗ₜ[k] a) = σ s ⊗ₜ[k] a := rfl

variable [Fintype k] (p a : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ a)

theorem relative_scalar (z : T) :
    Witt.BaseChangeNaturality.tensorMap k Ω A (FiniteField.frobeniusAlgHom k A) z =
      (scalarMap k A (Frobenius.Geometry.geometricFrobenius p a k hcard) z) ^ Fintype.card k := by
  have h : (Witt.BaseChangeNaturality.tensorMap k Ω A (FiniteField.frobeniusAlgHom k A)).restrictScalars k =
      (FiniteField.frobeniusAlgHom k T).comp
        (scalarMap k A (Frobenius.Geometry.geometricFrobenius p a k hcard)) := by
    apply Algebra.TensorProduct.ext'
    intro s b
    change s ⊗ₜ[k] (b ^ Fintype.card k) =
      (Frobenius.Geometry.geometricFrobenius p a k hcard s ⊗ₜ[k] b) ^ Fintype.card k
    rw [Algebra.TensorProduct.tmul_pow, hcard, Frobenius.Geometry.geometricFrobenius_pow]
  exact DFunLike.congr_fun h z

theorem comap (i : PrimeSpectrum T) :
    i.comap (Witt.BaseChangeNaturality.tensorMap k Ω A (FiniteField.frobeniusAlgHom k A)).toRingHom =
      i.comap (scalarMap k A (Frobenius.Geometry.geometricFrobenius p a k hcard)).toRingHom := by
  apply PrimeSpectrum.ext
  ext z
  change Witt.BaseChangeNaturality.tensorMap k Ω A (FiniteField.frobeniusAlgHom k A) z ∈ i.asIdeal ↔
    scalarMap k A (Frobenius.Geometry.geometricFrobenius p a k hcard) z ∈ i.asIdeal
  rw [relative_scalar k A p a hcard]
  exact i.isPrime.pow_mem_iff_mem (Fintype.card k) Fintype.card_pos

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FrobeniusAlgebra
