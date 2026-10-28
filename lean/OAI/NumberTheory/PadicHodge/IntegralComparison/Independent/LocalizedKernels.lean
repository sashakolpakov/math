import Mathlib.Algebra.Category.ModuleCat.Localization

/-! # Localized Kernels -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.LocalizedKernels

noncomputable section

universe u

variable {R : Type u} [CommRing R] {M N M' N' : ModuleCat.{u} R}
  (f : M →ₗ[R] N) (f' : M' →ₗ[R] N') (lM : M →ₗ[R] M') (lN : N →ₗ[R] N')
  (h : ∀ x, f' (lM x) = lN (f x))

def map : LinearMap.ker f →ₗ[R] LinearMap.ker f' where
  toFun x := ⟨lM x, by rw [LinearMap.mem_ker, h, x.2, map_zero]⟩
  map_add' x y := Subtype.ext (lM.map_add x y)
  map_smul' r x := Subtype.ext (lM.map_smul r x)

theorem isLocalized (S : Submonoid R) [IsLocalizedModule S lM] [IsLocalizedModule S lN] :
    IsLocalizedModule S (map f f' lM lN h) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact IsLocalizedModule.smul_injective lM s (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx⟩ := ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units lM s)).surjective y.1
      change s • x = y.1 at hx
      have hxker : f' x = 0 := by
        apply IsLocalizedModule.smul_injective lN s
        change s • f' x = s • (0 : N')
        rw [smul_zero, ← f'.map_smul_of_tower, hx]
        exact y.2
      exact ⟨⟨x, hxker⟩, Subtype.ext hx⟩
  surj y := by
    obtain ⟨⟨x, s⟩, hx⟩ := IsLocalizedModule.surj S lM y.1
    have hz : lN (f x) = 0 := by
      rw [← h, ← hx, f'.map_smul_of_tower, y.2, smul_zero]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff S lN).mp hz
    have hxker : f (t • x) = 0 := by rw [f.map_smul_of_tower]; exact ht
    refine ⟨(⟨t • x, hxker⟩, t * s), Subtype.ext ?_⟩
    change (t * s) • y.1 = lM (t • x)
    rw [mul_smul, hx, lM.map_smul_of_tower]
  exists_of_eq hxy := by
    have heq : lM _ = lM _ := congrArg Subtype.val hxy
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists S lM).mp heq
    exact ⟨s, Subtype.ext hs⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.LocalizedKernels
