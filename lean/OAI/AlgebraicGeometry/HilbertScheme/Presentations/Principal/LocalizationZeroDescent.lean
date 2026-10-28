import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.PrimeLocalization

/-! # Localization Zero Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.LocalizationZeroDescent

noncomputable section

/-! Finitely many equations which hold at a prime already hold after
shrinking a principal neighborhood of that prime. -/

open scoped BigOperators

universe u v
variable {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]

theorem principalToPrime_kernel_coefficient (s : A) (hs : s ∉ p)
    (x : Localization.Away s) (hx : PrimeLocalization.principalToPrimeMap p s hs x = 0) :
    ∃ t : p.primeCompl, algebraMap A (Localization.Away s) t.val * x = 0 := by
  obtain ⟨a, d, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers s) x
  have hn := congrArg (PrimeLocalization.principalToPrimeMap p s hs)
    (IsLocalization.mk'_spec (Localization.Away s) a d)
  simp only [map_mul, hx, zero_mul, PrimeLocalization.principalToPrimeMap_algebraMap] at hn
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) a).mp hn.symm
  refine ⟨t, ?_⟩
  apply (IsLocalization.map_units (Localization.Away s) d).mul_left_injective
  dsimp only
  rw [zero_mul, mul_assoc, IsLocalization.mk'_spec, ← map_mul, ht, map_zero]

theorem finite_principalToPrime_kernel_coefficient {κ : Type v} [Fintype κ]
    (s : A) (hs : s ∉ p) (x : κ → Localization.Away s)
    (hx : ∀ i, PrimeLocalization.principalToPrimeMap p s hs (x i) = 0) :
    ∃ t : p.primeCompl, ∀ i, algebraMap A (Localization.Away s) t.val * x i = 0 := by
  classical
  choose t ht using fun i => principalToPrime_kernel_coefficient p s hs (x i) (hx i)
  let z : p.primeCompl := ∏ i, t i
  refine ⟨z, fun i => ?_⟩
  have hd : (t i).val ∣ z.val := by
    change (t i).val ∣ (∏ j, t j : p.primeCompl).val
    rw [Submonoid.coe_finsetProd]
    exact Finset.dvd_prod_of_mem (fun j => (t j).val) (Finset.mem_univ i)
  obtain ⟨a, ha⟩ := hd
  rw [ha, map_mul, mul_right_comm, ht i, zero_mul]

def principalRefinementMap (s t : A) : Localization.Away s →+* Localization.Away (s * t) :=
  IsLocalization.Away.awayToAwayRight s t

@[simp] theorem principalRefinementMap_algebraMap (s t a : A) :
    principalRefinementMap s t (algebraMap A (Localization.Away s) a) =
      algebraMap A (Localization.Away (s * t)) a := IsLocalization.Away.awayToAwayRight_eq _ _ _

theorem principalRefinementMap_toPrime (s t : A) (hs : s ∉ p) (ht : t ∉ p) :
    (PrimeLocalization.principalToPrimeMap p (s * t) (p.primeCompl.mul_mem hs ht)).comp
      (principalRefinementMap s t) = PrimeLocalization.principalToPrimeMap p s hs := by
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, principalRefinementMap_algebraMap, PrimeLocalization.principalToPrimeMap_algebraMap]
  exact PrimeLocalization.principalToPrimeMap_algebraMap p (s * t) _ a

theorem finite_principalLocalization_zero_descent {κ : Type v} [Fintype κ]
    (s : A) (hs : s ∉ p) (x : κ → Localization.Away s)
    (hx : ∀ i, PrimeLocalization.principalToPrimeMap p s hs (x i) = 0) :
    ∃ t : A, t ∉ p ∧ ∀ i, principalRefinementMap s t (x i) = 0 := by
  obtain ⟨t, ht⟩ := finite_principalToPrime_kernel_coefficient p s hs x hx
  refine ⟨t.val, t.property, fun i => ?_⟩
  have h := congrArg (principalRefinementMap s t.val) (ht i)
  simp only [map_mul, principalRefinementMap_algebraMap, map_zero] at h
  have hu : IsUnit (algebraMap A (Localization.Away (s * t.val)) t.val) :=
    IsLocalization.Away.isUnit_of_dvd (s * t.val) (dvd_mul_left t.val s)
  exact hu.mul_right_injective (h.trans (mul_zero _).symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.LocalizationZeroDescent
