import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Maps
import Mathlib.RingTheory.Localization.Ideal

/-! # Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Localization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: localization of affine deformation algebras

The deformation algebra commutes with localization of its base ring. The
proof uses localized ideal-power membership for surjectivity and a finite
product of coefficient annihilators for injectivity. It permits zero divisors
and does not require finite generation of the ideal.
-/

open scoped BigOperators

universe u v
variable {R : Type u} [CommRing R]
variable (I : Ideal R) (M : Submonoid R)
variable (S : Type v) [CommRing S] [Algebra R S] [IsLocalization M S]

/-- The ideal after localization of the base. -/
abbrev localizedDeformationIdeal : Ideal S := I.map (algebraMap R S)

/-- Base-ring denominators viewed as constants in the deformation algebra. -/
def deformationDenominators : Submonoid (Iff.BundleCycles.deformationAlgebra I) :=
  M.map (algebraMap R (Iff.BundleCycles.deformationAlgebra I))

/-- Localization of the original deformation by base-ring denominators. -/
abbrev LocalizedDeformation := Localization (deformationDenominators I M)

/-- The coefficient map to the deformation of the localized ideal. -/
def deformationBaseMap : Iff.BundleCycles.deformationAlgebra I →+*
    Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S) :=
  Maps.BundleCycles.deformationMap I _ (algebraMap R S) (fun _ hr => Ideal.mem_map_of_mem _ hr)

theorem deformationBaseMap_units (m : deformationDenominators I M) :
    IsUnit (deformationBaseMap I S m) := by
  obtain ⟨r, hr, he⟩ := m.property
  change algebraMap R (Iff.BundleCycles.deformationAlgebra I) r = m.val at he
  rw [← he]
  change IsUnit (Maps.BundleCycles.deformationMap I _ (algebraMap R S) _ (algebraMap R _ r))
  exact (Maps.BundleCycles.deformationMap_algebraMap I _ (algebraMap R S) _ r).symm ▸
    (IsLocalization.map_units S (⟨r, hr⟩ : M)).map
      (algebraMap S (Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S)))

/-- Canonical map from the localized deformation to the deformation after
localizing its base ring. -/
def deformationLocalizationMap : LocalizedDeformation I M →+*
    Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S) :=
  IsLocalization.lift (deformationBaseMap_units I M S)

@[simp]
theorem deformationLocalizationMap_algebraMap (p : Iff.BundleCycles.deformationAlgebra I) :
    deformationLocalizationMap I M S (algebraMap _ (LocalizedDeformation I M) p) =
      deformationBaseMap I S p := IsLocalization.lift_eq _ p

/-- A Laurent monomial over the localized ideal lifts as a fraction of an
actual monomial over I. -/
theorem deformationLocalizationMap_monomial_mem_range (n : ℤ) (a : S)
    (ha : a ∈ localizedDeformationIdeal I S ^ (-n).toNat) :
    Iff.BundleCycles.deformationMonomial (localizedDeformationIdeal I S) n a ha ∈
      (deformationLocalizationMap I M S).rangeS := by
  have ha' : a ∈ (I ^ (-n).toNat).map (algebraMap R S) := by
    rwa [Ideal.map_pow]
  obtain ⟨⟨b, m⟩, hm⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp ha'
  let q : Iff.BundleCycles.deformationAlgebra I := Iff.BundleCycles.deformationMonomial I n b.val b.property
  let d : deformationDenominators I M :=
    ⟨algebraMap R _ m.val, Submonoid.mem_map_of_mem _ m.property⟩
  refine ⟨IsLocalization.mk' (LocalizedDeformation I M) q d, ?_⟩
  apply (IsLocalization.lift_mk'_spec (deformationBaseMap_units I M S) q _ d).mpr
  apply Subtype.ext
  change AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S) (AddMonoidAlgebra.single n b.val) =
    AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S) (AddMonoidAlgebra.single 0 m.val) *
      AddMonoidAlgebra.single n a
  rw [AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.mapRingHom_single,
    AddMonoidAlgebra.single_mul_single, zero_add, ← hm, mul_comm a]

/-- Every element of the deformation over the localized base has a preimage. -/
theorem deformationLocalizationMap_surjective :
    Function.Surjective (deformationLocalizationMap I M S) := by
  classical
  intro p
  have he : p = ∑ n ∈ p.val.coeff.support,
      Iff.BundleCycles.deformationMonomial (localizedDeformationIdeal I S) n (p.val.coeff n) (p.property n) := by
    apply Subtype.ext
    change p.val = (Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S)).val
      (∑ n ∈ p.val.coeff.support, Iff.BundleCycles.deformationMonomial _ n _ (p.property n))
    rw [map_sum]
    exact (AddMonoidAlgebra.sum_coeff_single p.val).symm
  have hp : p ∈ (deformationLocalizationMap I M S).rangeS := by
    rw [he]
    exact Subsemiring.sum_mem _ fun n _ =>
      deformationLocalizationMap_monomial_mem_range I M S n _ (p.property n)
  exact hp

/-- A coefficientwise zero after localization is annihilated by one common
base denominator. The product is finite because the Laurent support is finite. -/
theorem deformationBaseMap_zero_denominator (p : Iff.BundleCycles.deformationAlgebra I)
    (hp : deformationBaseMap I S p = 0) :
    ∃ m : M, algebraMap R (Iff.BundleCycles.deformationAlgebra I) m.val * p = 0 := by
  classical
  have hc (n : ℤ) : algebraMap R S (p.val.coeff n) = 0 := by
    have h := congrArg (fun q : Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S) =>
      q.val.coeff n) hp
    exact h
  have hm (n : ℤ) := (IsLocalization.map_eq_zero_iff M S (p.val.coeff n)).mp (hc n)
  choose m hm using hm
  let d : M := ∏ n ∈ p.val.coeff.support, m n
  refine ⟨d, Subtype.ext ?_⟩
  ext n
  change (AddMonoidAlgebra.single 0 d.val * p.val).coeff n = 0
  rw [AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add]
  by_cases hn : n ∈ p.val.coeff.support
  · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m hn
    have hd : d = m n * c := hc
    change d.val * p.val.coeff n = 0
    rw [hd]
    change (m n).val * c.val * p.val.coeff n = 0
    rw [mul_right_comm, hm n, zero_mul]
  · rw [Finsupp.notMem_support_iff.mp hn, mul_zero]

/-- No additional relations appear under the coefficientwise localization. -/
theorem deformationLocalizationMap_injective :
    Function.Injective (deformationLocalizationMap I M S) := by
  apply (IsLocalization.lift_injective_iff (deformationBaseMap_units I M S)).mpr
  intro p q
  constructor
  · intro h
    exact (deformationLocalizationMap_algebraMap I M S p).symm.trans
      ((congrArg (deformationLocalizationMap I M S) h).trans
        (deformationLocalizationMap_algebraMap I M S q))
  · intro h
    have hz : deformationBaseMap I S (p - q) = 0 := by
      rw [map_sub, h, sub_self]
    obtain ⟨m, hm⟩ := deformationBaseMap_zero_denominator I M S (p - q) hz
    apply (IsLocalization.eq_iff_exists (deformationDenominators I M)
      (LocalizedDeformation I M)).mpr
    refine ⟨⟨algebraMap R _ m.val, Submonoid.mem_map_of_mem _ m.property⟩, ?_⟩
    exact sub_eq_zero.mp ((mul_sub _ p q).symm.trans hm)

/-- Formation of the extended Rees algebra commutes with arbitrary base
localization. In particular it commutes with affine basic-open restriction. -/
def deformationLocalizationEquiv : LocalizedDeformation I M ≃+*
    Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S) :=
  RingEquiv.ofBijective (deformationLocalizationMap I M S)
    ⟨deformationLocalizationMap_injective I M S, deformationLocalizationMap_surjective I M S⟩

@[simp]
theorem deformationLocalizationEquiv_algebraMap (p : Iff.BundleCycles.deformationAlgebra I) :
    deformationLocalizationEquiv I M S (algebraMap _ (LocalizedDeformation I M) p) =
      deformationBaseMap I S p := deformationLocalizationMap_algebraMap I M S p

/-- The coefficient map exhibits the localized deformation as a localization,
with its specified algebra structure. -/
theorem deformationBaseMap_isLocalization :
    letI := (deformationBaseMap I S).toAlgebra
    IsLocalization (deformationDenominators I M)
      (Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S)) := by
  let := (deformationBaseMap I S).toAlgebra
  let e : LocalizedDeformation I M ≃ₐ[Iff.BundleCycles.deformationAlgebra I]
      Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S) :=
    { deformationLocalizationEquiv I M S with
      commutes' := deformationLocalizationEquiv_algebraMap I M S }
  exact IsLocalization.isLocalization_of_algEquiv (deformationDenominators I M) e

/-- Localization comparison for an ideal presented by an equality, as occurs
when restricting an ideal sheaf to an affine basic open. -/
theorem deformationMap_isLocalization (J : Ideal S)
    (hJ : I.map (algebraMap R S) = J) (hf : I ≤ J.comap (algebraMap R S)) :
    letI := (Maps.BundleCycles.deformationMap I J (algebraMap R S) hf).toAlgebra
    IsLocalization (deformationDenominators I M) (Iff.BundleCycles.deformationAlgebra J) := by
  subst J
  exact deformationBaseMap_isLocalization I M S

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Localization.BundleCycles
