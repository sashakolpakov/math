import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Local
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! # Integral Pairing Lattices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralPairingLattices

noncomputable section

/-! A perfect integral pairing identifies the images of its two modules
as dual lattices, once the ambient rational form agrees with its values.
The integral dual-lattice identity is proved from the pairing map. -/

variable {R K U V W : Type*} [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [Module.IsTorsionFree R K]
  [AddCommGroup U] [Module R U] [Module K U] [IsScalarTower R K U]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  (B : LinearMap.BilinForm K U) (L M : Submodule R U)
  (eV : V ≃ₗ[R] L) (eW : W ≃ₗ[R] M)
  (β : W →ₗ[R] V →ₗ[R] R)
  (hB : ∀ (y : W) (x : V), B (eW y).val (eV x).val = algebraMap R K (β y x))

include hB in
omit [IsDomain R] [Module.IsTorsionFree R K] in
theorem integralPairing_image_le_dual : M ≤ B.dualSubmodule L := by
  intro y hy x hx
  apply Submodule.mem_one.mpr
  refine ⟨β (eW.symm ⟨y, hy⟩) (eV.symm ⟨x, hx⟩), ?_⟩
  have h := hB (eW.symm ⟨y, hy⟩) (eV.symm ⟨x, hx⟩)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

include hB in
theorem integralPairing_latticePairingMap (hIntegral : M ≤ B.dualSubmodule L)
    (y : W) (x : V) :
    Local.latticePairingMap B L M hIntegral (eW y) (eV x) = β y x := by
  apply FaithfulSMul.algebraMap_injective R K
  change algebraMap R K
    (B.dualSubmoduleParing (Submodule.inclusion hIntegral (eW y)) (eV x)) = _
  rw [B.dualSubmoduleParing_spec]
  exact hB y x

include hB in
theorem perfectLatticePairing_of_integralPairing (hβ : Function.Bijective β) :
    Local.IsPerfectLatticePairing B L M := by
  let hIntegral := integralPairing_image_le_dual B L M eV eW β hB
  refine ⟨hIntegral, ?_⟩
  have hmap : Local.latticePairingMap B L M hIntegral =
      eV.symm.dualMap.toLinearMap.comp (β.comp eW.symm.toLinearMap) := by
    apply LinearMap.ext
    intro y
    obtain ⟨y, rfl⟩ := eW.surjective y
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := eV.surjective x
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, LinearEquiv.dualMap_apply] using
      integralPairing_latticePairingMap B L M eV eW β hB hIntegral y x
  rw [hmap]
  exact eV.symm.dualMap.bijective.comp (hβ.comp eW.symm.bijective)

include hB in
theorem integralPairing_image_eq_dual (hβ : Function.Bijective β)
    (hBnd : B.Nondegenerate) (hL : Submodule.span K (L : Set U) = ⊤) :
    M = B.dualSubmodule L :=
  Local.perfectLatticePairing_forces_dual B hBnd L M hL
    (perfectLatticePairing_of_integralPairing B L M eV eW β hB hβ)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralPairingLattices
