import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Homology Injective -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.HomologyInjective

noncomputable section

/-! Injectivity on homology expressed by detection of boundaries. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.HomologyInjectiveCriterion

variable {R : Type u} [CommRing R]
variable {S T : ShortComplex (ModuleCat.{u} R)} (φ : S ⟶ T)

theorem injective
    (h : ∀ z : S.X₂, S.g z = 0 → φ.τ₂ z ∈ T.f.hom.range → z ∈ S.f.hom.range) :
    Function.Injective (ShortComplex.homologyMap φ) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance x
  have hz : T.pOpcycles (φ.τ₂ (S.iCycles z)) = 0 := by
    have he := congrArg (fun y => T.homologyι y) hx
    change (S.homologyπ ≫ ShortComplex.homologyMap φ ≫ T.homologyι) z = _ at he
    rw [ShortComplex.π_homologyMap_ι] at he
    simpa only [ModuleCat.comp_apply, map_zero] using he
  have hg : S.g (S.iCycles z) = 0 := by
    change (S.iCycles ≫ S.g) z = 0
    rw [S.iCycles_g]
    rfl
  have hb := h (S.iCycles z) hg ((T.moduleCat_pOpcycles_eq_zero_iff _).mp hz)
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  change (S.homologyπ ≫ S.homologyι) z = _
  rw [S.homology_π_ι]
  simpa only [ModuleCat.comp_apply, map_zero] using
    (S.moduleCat_pOpcycles_eq_zero_iff _).mpr hb

theorem boundary (hi : Function.Injective (ShortComplex.homologyMap φ))
    (z : S.X₂) (hz : S.g z = 0) (hb : φ.τ₂ z ∈ T.f.hom.range) :
    z ∈ S.f.hom.range := by
  let c := S.cyclesMk z hz
  have hc : S.iCycles c = z := S.i_cyclesMk z hz
  have hzero : ShortComplex.homologyMap φ (S.homologyπ c) = 0 := by
    apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
    change (S.homologyπ ≫ ShortComplex.homologyMap φ ≫ T.homologyι) c = T.homologyι 0
    rw [ShortComplex.π_homologyMap_ι]
    simpa only [ModuleCat.comp_apply, hc, map_zero] using
      (T.moduleCat_pOpcycles_eq_zero_iff _).mpr hb
  have hclass : S.homologyπ c = 0 := hi (hzero.trans (map_zero _).symm)
  apply (S.moduleCat_pOpcycles_eq_zero_iff z).mp
  have he := ConcreteCategory.congr_hom S.homology_π_ι c
  change S.homologyι (S.homologyπ c) = S.pOpcycles (S.iCycles c) at he
  rw [hclass, map_zero, hc] at he
  exact he.symm

theorem iff_boundary : Function.Injective (ShortComplex.homologyMap φ) ↔
    ∀ z : S.X₂, S.g z = 0 → φ.τ₂ z ∈ T.f.hom.range → z ∈ S.f.hom.range :=
  ⟨boundary φ, injective φ⟩

end Construction.HomologyInjectiveCriterion

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.HomologyInjective
