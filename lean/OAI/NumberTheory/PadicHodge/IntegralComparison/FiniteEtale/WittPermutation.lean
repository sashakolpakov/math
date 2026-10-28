import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.WittSplitting
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.BaseChangeNaturality

/-! # Witt Permutation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.WittPermutation

noncomputable section

/-! The actual split Witt action is precomposition by the induced map on geometric prime ideals. -/

open scoped TensorProduct

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

universe u

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [CommRing A] [Algebra k A]
  [CharP k p] [PerfectRing k p] [Nontrivial A] [Module.Finite k A] [Algebra.Etale k A]

local notation "Ω" => AlgebraicClosure k
local notation "T" => Ω ⊗[k] A

theorem natural (f : A →ₐ[k] A)
    (z : (WittVector p Ω) ⊗[WittVector p k] (WittVector p A)) (i : PrimeSpectrum T) :
    WittSplitting.equiv p k A
      ((PeriodInvariants.WittAlgebraFunctor.map p k f).toLinearMap.baseChange (WittVector p Ω) z) i =
        WittSplitting.equiv p k A z
          (i.comap (Witt.BaseChangeNaturality.tensorMap k Ω A f)) := by
  apply WittVector.ext
  intro n
  rw [WittSplitting.coeff, WittSplitting.coeff,
    Witt.BaseChangeNaturality.natural]
  exact (Algebra.FormallyEtale.equivPiOfIsSepClosed_comap
    (Witt.BaseChangeNaturality.tensorMap k Ω A f)
    ((Witt.BaseChangeNaturality.Finite.map p k Ω A z).coeff n) i).symm

omit p [Fact p.Prime] [CharP k p] [PerfectRing k p] [Nontrivial A]
    [Module.Finite k A] [Algebra.Etale k A] in
def permutation (e : A ≃ₐ[k] A) : Equiv.Perm (PrimeSpectrum T) :=
  (PrimeSpectrum.comapEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : Ω ≃ₐ[Ω] Ω) e).symm.toRingEquiv).toEquiv

theorem action (e : A ≃ₐ[k] A)
    (z : (WittVector p Ω) ⊗[WittVector p k] (WittVector p A)) (i : PrimeSpectrum T) :
    WittSplitting.equiv p k A
      ((PeriodInvariants.WittAlgebraFunctor.map p k e.toAlgHom).toLinearMap.baseChange (WittVector p Ω) z) i =
        WittSplitting.equiv p k A z (permutation k A e i) :=
  natural p k A e.toAlgHom z i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.WittPermutation
