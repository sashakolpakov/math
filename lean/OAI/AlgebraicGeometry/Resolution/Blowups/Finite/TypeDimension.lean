import OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralDimension
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! # Type Dimension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.TypeDimension.Construction

noncomputable section

/-! Dimension comparisons for finite-type chart rings in arbitrary universes. -/

universe u

/-- Noether normalization computes the dimension of a finite-type domain
over the ground field, with no restriction to universe zero. -/
theorem finiteType_domain_ringKrullDim_eq_trdeg (k A : Type u) [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A = ((Algebra.trdeg k A).toNat : WithBot ℕ∞) := by
  obtain ⟨n, f, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let : Algebra P A := f.toRingHom.toAlgebra
  let : Algebra.IsIntegral P A := ⟨hint⟩
  let : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  let : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' (by
    ext c
    exact (f.commutes c).symm)
  have hd : ringKrullDim A = (n : WithBot ℕ∞) := by
    rw [DivisorClass.Chern.IntegralDimension.Construction.integral_ringKrullDim_eq (R := P) (S := A) hinj]
    change ringKrullDim (MvPolynomial (Fin n) k) = _
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      zero_add, ENat.card_eq_coe_fintype_card, Fintype.card_fin, WithBot.coe_natCast]
  have ht : (n : Cardinal) = Algebra.trdeg k A := by
    have h := trdeg_add_eq k P (A := A)
    rw [trdeg_eq_zero (R := P) (A := A), add_zero] at h
    change Algebra.trdeg k (MvPolynomial (Fin n) k) = _ at h
    simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_natCast] using h
  rw [hd, ← ht, Cardinal.toNat_natCast]

/-- An actual embedding between finite-type domains cannot decrease
transcendence degree and therefore cannot decrease Krull dimension. -/
theorem finiteType_domain_ringKrullDim_le_of_injective (k : Type u) [Field k]
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra k A] [Algebra k B] [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    (f : A →ₐ[k] B) (hf : Function.Injective f) : ringKrullDim A ≤ ringKrullDim B := by
  rw [finiteType_domain_ringKrullDim_eq_trdeg k A, finiteType_domain_ringKrullDim_eq_trdeg k B]
  exact_mod_cast Cardinal.toNat_le_toNat (trdeg_le_of_injective f hf)
    (trdeg_lt_aleph0_of_finiteType (R := k) (S := B))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.TypeDimension.Construction
