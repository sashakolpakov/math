import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Module Squares -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.ModuleSquares

noncomputable section

/-! Localization is invariant under a commutative square of module isomorphisms. -/

variable {R V W V' W' : Type*} [CommRing R]
variable [AddCommGroup V] [AddCommGroup W] [AddCommGroup V'] [AddCommGroup W']
variable [Module R V] [Module R W] [Module R V'] [Module R W']

theorem isLocalizedModule_of_linearEquiv_square (S : Submonoid R)
    (a : V →ₗ[R] W) (b : V' →ₗ[R] W') (eV : V ≃ₗ[R] V') (eW : W ≃ₗ[R] W')
    (h : eW.toLinearMap.comp a = b.comp eV.toLinearMap) [IsLocalizedModule S a] :
    IsLocalizedModule S b := by
  have : IsLocalizedModule S (a.comp eV.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S a eV.symm
  have ht := IsLocalizedModule.of_linearEquiv S (a.comp eV.symm.toLinearMap) eW
  have he : eW.toLinearMap.comp (a.comp eV.symm.toLinearMap) = b := by
    ext x
    have hx := LinearMap.congr_fun h (eV.symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, eV.apply_symm_apply] at hx
    exact hx
  rw [he] at ht
  exact ht

theorem isLocalizedModule_iff_of_linearEquiv_square (S : Submonoid R)
    (a : V →ₗ[R] W) (b : V' →ₗ[R] W') (eV : V ≃ₗ[R] V') (eW : W ≃ₗ[R] W')
    (h : eW.toLinearMap.comp a = b.comp eV.toLinearMap) :
    IsLocalizedModule S a ↔ IsLocalizedModule S b := by
  constructor
  · intro ha
    exact isLocalizedModule_of_linearEquiv_square S a b eV eW h
  · intro hb
    apply isLocalizedModule_of_linearEquiv_square S b a eV.symm eW.symm
    ext x
    apply eW.injective
    have hx := LinearMap.congr_fun h (eV.symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, eV.apply_symm_apply] at hx
    exact (eW.apply_symm_apply (b x)).trans hx.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.ModuleSquares
