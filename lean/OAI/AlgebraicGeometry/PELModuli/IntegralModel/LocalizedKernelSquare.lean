import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-! # Localized Kernel Square -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalizedKernelSquare

noncomputable section

/-! Localization passes through the actual kernel map of a commuting
square. This form does not require chosen module structures over a
localized coefficient ring. -/

universe u v w v' w'
variable {R : Type u} [CommRing R] (S : Submonoid R)
    {M : Type v} {N : Type w} {M' : Type v'} {N' : Type w'}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module R M'] [Module R N']
    (a : M →ₗ[R] M') (b : N →ₗ[R] N')
    [IsLocalizedModule S a] [IsLocalizedModule S b]
    (d : M →ₗ[R] N) (d' : M' →ₗ[R] N')
    (h : d'.comp a = b.comp d)

def kernelSquareMap : d.ker →ₗ[R] d'.ker :=
  a.restrict (fun x hx => by
    change d' (a x) = 0
    rw [← LinearMap.comp_apply, h, LinearMap.comp_apply, hx, map_zero])

theorem kernelSquareMap_isLocalized :
    IsLocalizedModule S (kernelSquareMap a b d d' h) := by
  let : Module (Localization S) M' := IsLocalizedModule.module S a
  let : Module (Localization S) N' := IsLocalizedModule.module S b
  let : IsScalarTower R (Localization S) M' := IsLocalizedModule.isScalarTower_module S a
  let : IsScalarTower R (Localization S) N' := IsLocalizedModule.isScalarTower_module S b
  have hd : IsLocalizedModule.map S a b d = d' := by
    apply IsLocalizedModule.linearMap_ext S a b
    rw [IsLocalizedModule.map_comp, h]
  let e : (IsLocalizedModule.map S a b d).ker ≃ₗ[R] d'.ker :=
    LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hd)
  have hi : IsLocalizedModule S (LinearMap.toKerIsLocalized S a b d) :=
    LinearMap.toKerLocalized_isLocalizedModule (S := Localization S) S a b d
  let := hi
  have he := IsLocalizedModule.of_linearEquiv S (LinearMap.toKerIsLocalized S a b d) e
  convert he using 1
  ext x
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalizedKernelSquare
