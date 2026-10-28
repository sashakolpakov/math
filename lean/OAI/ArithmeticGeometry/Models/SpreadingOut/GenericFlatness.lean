import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange

/-! # Generic Flatness -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GenericFlatness.Construction

noncomputable section

/-! Generic flatness over a Dedekind domain, for finite modules over
noetherian algebras, by killing the finitely generated base torsion. -/

open scoped TensorProduct nonZeroDivisors

universe u

theorem base_torsion_killed_by_nonzero
    (R B M : Type u) [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    [IsNoetherian B M] :
    ∃ r : R, r ≠ 0 ∧ ∀ m : M, (∃ a : R, a ≠ 0 ∧ a • m = 0) → r • m = 0 := by
  classical
  let T := Submodule.torsion' B M R⁰
  obtain ⟨s, hs⟩ := (inferInstance : IsNoetherian B M).noetherian T
  have H (x : s) : ∃ a : R⁰, a • (x : M) = 0 := by
    change (x : M) ∈ T
    rw [← hs]
    exact Submodule.subset_span x.property
  choose a ha using H
  let r : R⁰ := ∏ x : s, a x
  have hr (x : s) : r • (x : M) = 0 := by
    dsimp only [r]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ x), mul_smul, ha, smul_zero]
  have hT : T ≤ (DistribSMul.toLinearMap B M r).ker := by
    rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    exact hr ⟨x, hx⟩
  refine ⟨r, nonZeroDivisors.coe_ne_zero r, fun m hm ↦ ?_⟩
  apply hT
  obtain ⟨a, ha, ham⟩ := hm
  exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ham⟩

theorem localized_torsionFree_of_torsion_killed
    (R M N : Type u) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (r : R) (hr : r ≠ 0)
    (hkill : ∀ m : M, (∃ a : R, a ≠ 0 ∧ a • m = 0) → r • m = 0)
    (f : M →ₗ[R] N) [IsLocalizedModule (Submonoid.powers r) f] :
    Module.IsTorsionFree R N := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro a y hay
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers r) f y
  have ham : f (a • m) = 0 := by
    rw [map_smul, ← hs, smul_comm, hay, smul_zero]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers r) f).mp ham
  have htm : ((t : R) * a) • m = 0 := by
    simpa only [mul_smul, Submonoid.smul_def] using ht
  have ht0 : (t : R) ≠ 0 := by
    obtain ⟨n, hn⟩ := t.property
    rw [← hn]
    exact pow_ne_zero n hr
  have hfm : f m = 0 := by
    apply (IsLocalizedModule.eq_zero_iff (Submonoid.powers r) f).mpr
    exact ⟨⟨r, Submonoid.mem_powers r⟩, hkill m ⟨_, mul_ne_zero ht0 ha, htm⟩⟩
  apply (IsLocalizedModule.smul_injective f s)
  simpa only [smul_zero] using hs.trans hfm

theorem finite_module_flat_after_inverting_nonzero
    (R B M : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [Algebra R B] [AddCommGroup M] [Module R M] [Module B M]
    [IsScalarTower R B M] [IsNoetherian B M] :
    ∃ r : R, r ≠ 0 ∧ Module.Flat R (Localization.Away r ⊗[R] M) := by
  obtain ⟨r, hr, hkill⟩ := base_torsion_killed_by_nonzero R B M
  have : Module.IsTorsionFree R (Localization.Away r ⊗[R] M) :=
    localized_torsionFree_of_torsion_killed R M _ r hr hkill
      (TensorProduct.mk R (Localization.Away r) M 1)
  exact ⟨r, hr, inferInstance⟩

theorem finite_module_flat_over_localization
    (R B M : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [Algebra R B] [AddCommGroup M] [Module R M] [Module B M]
    [IsScalarTower R B M] [IsNoetherian B M] :
    ∃ r : R, r ≠ 0 ∧
      Module.Flat (Localization.Away r) (Localization.Away r ⊗[R] M) := by
  obtain ⟨r, hr, hf⟩ := finite_module_flat_after_inverting_nonzero R B M
  exact ⟨r, hr, (Module.flat_iff_of_isLocalization (Localization.Away r)
    (Submonoid.powers r) _).mpr hf⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GenericFlatness.Construction
