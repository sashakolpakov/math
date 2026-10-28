import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Short Complex Of -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShortComplexOf.ShortComplexComparison

noncomputable section

/-! Concrete criteria for comparing the kernels and cokernels of short complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R]
variable {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T)

theorem opcycles_iso
    (hs : ∀ y : T.X₂, ∃ x : S.X₂, ∃ z : T.X₁, φ.τ₂ x + T.f z = y)
    (hi : ∀ x : S.X₂, φ.τ₂ x ∈ T.f.hom.range → x ∈ S.f.hom.range) :
    IsIso (ShortComplex.opcyclesMap φ) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y hxy
    have hp : Function.Surjective S.pOpcycles :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    obtain ⟨a, rfl⟩ := hp x
    obtain ⟨b, rfl⟩ := hp y
    have hab : T.pOpcycles (φ.τ₂ a) = T.pOpcycles (φ.τ₂ b) := by
      simpa only [← ConcreteCategory.comp_apply, ShortComplex.p_opcyclesMap] using hxy
    apply (S.moduleCat_pOpcycles_eq_iff a b).mpr
    apply hi (a - b)
    simpa only [map_sub] using (T.moduleCat_pOpcycles_eq_iff _ _).mp hab
  · intro y
    obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective T.pOpcycles).mp inferInstance y
    obtain ⟨a, z, hz⟩ := hs b
    refine ⟨S.pOpcycles a, ?_⟩
    change (S.pOpcycles ≫ ShortComplex.opcyclesMap φ) a = T.pOpcycles b
    rw [ShortComplex.p_opcyclesMap]
    change T.pOpcycles (φ.τ₂ a) = T.pOpcycles b
    apply (T.moduleCat_pOpcycles_eq_iff _ _).mpr
    refine ⟨-z, ?_⟩
    rw [map_neg, ← hz]
    abel

theorem cycles_iso
    (hs : ∀ y : T.X₂, T.g y = 0 → ∃ x : S.X₂, S.g x = 0 ∧ φ.τ₂ x = y)
    (hi : ∀ x : S.X₂, S.g x = 0 → φ.τ₂ x = 0 → x = 0) :
    IsIso (ShortComplex.cyclesMap φ) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y hxy
    apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
    apply sub_eq_zero.mp
    apply hi (S.iCycles x - S.iCycles y)
    · rw [map_sub]
      change (S.iCycles ≫ S.g) x - (S.iCycles ≫ S.g) y = 0
      rw [S.iCycles_g]
      exact sub_self 0
    · have h := congrArg (fun z => T.iCycles z) hxy
      change (ShortComplex.cyclesMap φ ≫ T.iCycles) x =
        (ShortComplex.cyclesMap φ ≫ T.iCycles) y at h
      rw [ShortComplex.cyclesMap_i] at h
      rw [map_sub]
      exact sub_eq_zero.mpr h
  · intro y
    obtain ⟨a, ha, hay⟩ := hs (T.iCycles y) (by
      change (T.iCycles ≫ T.g) y = 0
      rw [T.iCycles_g]
      rfl)
    refine ⟨S.cyclesMk a ha, ?_⟩
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    change (ShortComplex.cyclesMap φ ≫ T.iCycles) (S.cyclesMk a ha) = _
    rw [ShortComplex.cyclesMap_i]
    change φ.τ₂ (S.iCycles (S.cyclesMk a ha)) = _
    have hm : S.iCycles (S.cyclesMk a ha) = a := S.i_cyclesMk a ha
    rw [hm]
    exact hay

theorem quasiIso_of_cycles_iso (hS : S.f = 0) (hT : T.f = 0)
    [IsIso (ShortComplex.cyclesMap φ)] : ShortComplex.QuasiIso φ := by
  have := S.isIso_homologyπ hS
  have := T.isIso_homologyπ hT
  have : IsIso (S.homologyπ ≫ ShortComplex.homologyMap φ) := by
    rw [ShortComplex.homologyπ_naturality]
    infer_instance
  exact ⟨IsIso.of_isIso_comp_left S.homologyπ (ShortComplex.homologyMap φ)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShortComplexOf.ShortComplexComparison
