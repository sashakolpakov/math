import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ModuleAnnihilation
import Mathlib.RingTheory.Localization.Ideal

/-! # Annihilator Localization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AnnihilatorLocalization

noncomputable section

/-! The annihilator of a finite module commutes with actual localization. -/

open scoped BigOperators

universe u v w t

theorem finite_localization_exists_multiplier_annihilator
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (S : Submonoid R)
    {N : Type w} [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) [IsLocalizedModule S g] (a : R)
    (h : ∀ m : M, g (a • m) = 0) :
    ∃ s ∈ S, s * a ∈ Module.annihilator R M := by
  classical
  obtain ⟨s, hs⟩ := ‹Module.Finite R M›
  have hzero (m : s) : ∃ r ∈ S, r • (a • m.val) = 0 := by
    obtain ⟨r, hr⟩ := (IsLocalizedModule.eq_zero_iff S g).mp (h m.val)
    exact ⟨r, r.property, hr⟩
  choose r hr hrz using hzero
  refine ⟨s.attach.prod r, S.prod_mem (fun m _ => hr m), ?_⟩
  rw [← Submodule.annihilator_top, ← hs, Submodule.mem_annihilator_span]
  intro m
  obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem r (Finset.mem_attach s m)
  rw [mul_smul, hb, mul_comm, mul_smul, hrz, smul_zero]

theorem annihilator_map_eq_of_isLocalizedModule
    {R : Type u} [CommRing R] (S : Submonoid R)
    (A : Type t) [CommRing A] [Algebra R A] [IsLocalization S A]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (g : M →ₗ[R] N) [IsLocalizedModule S g] :
    (Module.annihilator R M).map (algebraMap R A) = Module.annihilator A N := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    apply Module.mem_annihilator.mpr
    intro y
    rw [IsScalarTower.algebraMap_smul]
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S g y
    change a • IsLocalizedModule.mk' g m s = 0
    rw [← IsLocalizedModule.mk'_smul, Module.mem_annihilator.mp ha m,
      IsLocalizedModule.mk'_zero]
  · apply (IsLocalization.under_le_under_iff S A).mp
    intro a ha
    change algebraMap R A a ∈ (Module.annihilator R M).map (algebraMap R A)
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff S A]
    apply finite_localization_exists_multiplier_annihilator S g a
    intro m
    rw [g.map_smul, ← IsScalarTower.algebraMap_smul A a (g m)]
    exact Module.mem_annihilator.mp ha (g m)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AnnihilatorLocalization
