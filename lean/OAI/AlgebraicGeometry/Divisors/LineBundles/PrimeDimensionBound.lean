import OAI.AlgebraicGeometry.DivisorClass.Chern.FiniteTypeDimension
import Mathlib.RingTheory.Ideal.Height

/-! # Prime Dimension Bound -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeDimensionBound.BundleCycles

noncomputable section

/-!
# LineBundleCycles: prime height plus quotient dimension is bounded by ambient dimension

This is the general chain-length inequality. Finite-type dimension
identification expresses it in the actual transcendence grading.
-/

open _root_.Order

theorem primeQuotient_ringKrullDim_eq_coheight {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] :
    ringKrullDim (R ⧸ P) = (coheight (⟨P, inferInstance⟩ : PrimeSpectrum R) : WithBot ℕ∞) := by
  let p : PrimeSpectrum R := ⟨P, inferInstance⟩
  have e : PrimeSpectrum (R ⧸ P) ≃o Set.Ici p := P.primeSpectrumQuotientOrderIsoZeroLocus
  exact (Order.krullDim_eq_of_orderIso e).trans (coheight_eq_krullDim_Ici p).symm

theorem primeHeight_add_quotient_dimension_le {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (R ⧸ P) ≤ ringKrullDim R := by
  let p : PrimeSpectrum R := ⟨P, inferInstance⟩
  let : Nonempty (PrimeSpectrum R) := ⟨p⟩
  rw [primeQuotient_ringKrullDim_eq_coheight, PrimeSpectrum.height_eq_orderHeight p]
  change ((height p + coheight p : ℕ∞) : WithBot ℕ∞) ≤ krullDim (PrimeSpectrum R)
  rw [krullDim_eq_iSup_height_add_coheight_of_nonempty, WithBot.coe_le_coe]
  exact le_iSup (fun q : PrimeSpectrum R => height q + coheight q) p

theorem finiteType_primeHeight_add_trdeg_le (k R : Type) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] (P : Ideal R) [P.IsPrime] :
    P.height + ((Algebra.trdeg k (R ⧸ P)).toNat : ℕ∞) ≤ ((Algebra.trdeg k R).toNat : ℕ∞) := by
  have h := primeHeight_add_quotient_dimension_le P
  rw [DivisorClass.Chern.FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg k (R ⧸ P),
    DivisorClass.Chern.FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg k R] at h
  exact WithBot.coe_le_coe.mp h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeDimensionBound.BundleCycles
