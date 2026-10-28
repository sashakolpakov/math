import Mathlib.LinearAlgebra.Prod

/-! # Transverse Projection Linear -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TransverseProjectionLinear.Constructions

/-! The linear transversality calculation for a normal slice and an immersion with injective base projection. -/

variable {k A F U W V : Type*} [Field k]
  [AddCommGroup A] [Module k A] [AddCommGroup F] [Module k F]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  [AddCommGroup V] [Module k V]

theorem normal_slice_injective (q : A →ₗ[k] U) (s : U →ₗ[k] A)
    (i : W →ₗ[k] A × F) (n : A × F →ₗ[k] V)
    (hs : q.comp s = LinearMap.id)
    (hn : LinearMap.ker n = LinearMap.range i)
    (hq : q.comp ((LinearMap.fst k A F).comp i) = 0)
    (hi : Function.Injective ((LinearMap.fst k A F).comp i)) :
    Function.Injective (n.comp (s.prodMap (LinearMap.id : F →ₗ[k] F))) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro v hv
  change v = 0
  have hv' : (s v.1, v.2) ∈ LinearMap.ker n := hv
  rw [hn] at hv'
  obtain ⟨w, hw⟩ := hv'
  have hqw := LinearMap.congr_fun hq w
  change q (i w).1 = 0 at hqw
  rw [hw] at hqw
  have hsv := LinearMap.congr_fun hs v.1
  change q (s v.1) = v.1 at hsv
  have hv₁ : v.1 = 0 := hsv.symm.trans hqw
  have hw₀ : w = 0 := hi (by
    change (i w).1 = (i 0).1
    rw [hw, hv₁, map_zero, map_zero]
    rfl)
  rw [hw₀, map_zero] at hw
  exact Prod.ext hv₁ (congrArg Prod.snd hw).symm

end OAI.AlgebraicGeometry.CycleClass.Thom.TransverseProjectionLinear.Constructions
