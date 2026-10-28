import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexDeterminantVanishing

/-! # Complex Determinant Effective -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexDeterminantEffective

noncomputable section

/-! The divisor of a generically exact length-two free complex is
effective: its determinant quotient is an actual element of the normal
domain, with order equal to the local cokernel length. -/

set_option backward.isDefEq.respectTransparency false

open _root_.Module _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct Classical

universe u v w

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
  {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]

local instance : DecidableEq (ι ⊕ κ) := Classical.decEq _

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexDeterminantBaseChange

theorem exists_equation (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : g.comp f = 0)
    (hf : Function.Injective f) (t : C →ₗ[R] B) (ht : Function.Injective (g.comp t))
    (a : Basis ι R A) (b : Basis (ι ⊕ κ) R B) (c : Basis κ R C)
    (hex : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      (ComplexDeterminantBaseChange.complex R (Localization.AtPrime p) f g h).Exact) :
    ∃ r : R, r ≠ 0 ∧ ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      Ring.ord (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) r) =
        Module.length (Localization.AtPrime p)
          (((Localization.AtPrime p) ⊗[R] C) ⧸ (g.baseChange (Localization.AtPrime p)).range) := by
  let d := (LinearMap.toMatrix (a.prod c) b (f.coprod t)).det
  let n := (g.comp t).det
  have hd : d ≠ 0 := InjectiveDeterminant.matrix_ne_zero R (a.prod c) b _
    (ShortComplexDeterminant.coprod_injective R f g h hf t ht)
  have hn : n ≠ 0 := InjectiveDeterminant.end_ne_zero R c _ ht
  have he (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
      Ring.ord (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) d) +
        Module.length (Localization.AtPrime p)
          (((Localization.AtPrime p) ⊗[R] C) ⧸ (g.baseChange (Localization.AtPrime p)).range) =
      Ring.ord (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) n) := by
    let S := Localization.AtPrime p
    let : IsDiscreteValuationRing S := NormalDivisibility.localization_dvr R p hp
    have hfS : Function.Injective (f.baseChange S) :=
      Module.Flat.lTensor_preserves_injective_linearMap f hf
    have htS : Function.Injective ((g.comp t).baseChange S) :=
      Module.Flat.lTensor_preserves_injective_linearMap (g.comp t) ht
    have hz : IsZero (ComplexDeterminantBaseChange.complex R S f g h).homology :=
      (ComplexDeterminantBaseChange.complex R S f g h).exact_iff_isZero_homology.mp (hex p hp)
    let : Subsingleton (ComplexDeterminantBaseChange.complex R S f g h).homology := ModuleCat.subsingleton_of_isZero hz
    have hh := ComplexDeterminantBaseChange.order_comparison R S f g h t hfS htS a b c
    have hzero : Module.length S (ComplexDeterminantBaseChange.complex R S f g h).homology = 0 := Module.length_eq_zero
    rw [hzero, zero_add] at hh
    exact hh
  have hdvd : d ∣ n := by
    apply NormalDivisibility.of_localizations R d n hd
    intro p hprime hp
    let S := Localization.AtPrime p
    let : IsDiscreteValuationRing S := NormalDivisibility.localization_dvr R p hp
    apply IsDiscreteValuationRing.addVal_le_iff_dvd.mp
    rw [← Ring.ord_eq_addVal, ← Ring.ord_eq_addVal, ← he p hp]
    exact le_self_add
  obtain ⟨r, hr⟩ := hdvd
  have hr₀ : r ≠ 0 := by
    intro hz
    apply hn
    rw [hr, hz, mul_zero]
  refine ⟨r, hr₀, ?_⟩
  intro p hprime hp
  let S := Localization.AtPrime p
  let : IsDiscreteValuationRing S := NormalDivisibility.localization_dvr R p hp
  have hi : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S p.primeCompl_le_nonZeroDivisors
  have hdS := (map_ne_zero_iff _ hi).mpr hd
  have hh := he p hp
  rw [hr, map_mul, Ring.ord_mul' S (mem_nonZeroDivisors_of_ne_zero hdS)] at hh
  exact (ENat.add_right_injective_of_ne_top
    (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hdS))) hh.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexDeterminantEffective
