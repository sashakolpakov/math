import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.Fractions
import Mathlib.RingTheory.Localization.BaseChange

/-! # Tensor Module Localization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorModuleLocalization.GradedModules

noncomputable section

/-! Tensoring an actual principal module localization commutes with localization of the tensor product. -/

open TensorProduct

universe u v w t

variable (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (S : Type t) [AddCommGroup S] [Module R S]

def awayModuleTensorEquiv (a : A) :
    Presentations.Module.Fractions.GradedModules.AwayModule a M ⊗[R] S ≃ₗ[R] Presentations.Module.Fractions.GradedModules.AwayModule a (M ⊗[R] S) := by
  let f := AlgebraTensorModule.rTensor R S (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
  exact (IsLocalizedModule.iso (Submonoid.powers a) f).symm.restrictScalars R

theorem awayModuleTensorEquiv_fraction (a : A) (k : ℕ) (m : M) (s : S) :
    awayModuleTensorEquiv R A M S a (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k m ⊗ₜ[R] s) =
      Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k (m ⊗ₜ[R] s) := by
  let f := AlgebraTensorModule.rTensor R S (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
  let E := IsLocalizedModule.iso (Submonoid.powers a) f
  change E.symm (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k m ⊗ₜ[R] s) = _
  apply E.injective
  rw [E.apply_symm_apply, Presentations.Module.Fractions.GradedModules.moduleFractionMap_apply, Presentations.Module.Fractions.GradedModules.moduleFractionMap_apply]
  change LocalizedModule.mk m (Presentations.Module.Fractions.GradedModules.moduleDenominator a k) ⊗ₜ[R] s =
    IsLocalizedModule.mk' f (m ⊗ₜ[R] s) (Presentations.Module.Fractions.GradedModules.moduleDenominator a k)
  rw [← IsLocalizedModule.smul_inj f (Presentations.Module.Fractions.GradedModules.moduleDenominator a k), IsLocalizedModule.mk'_cancel']
  change (a ^ k • LocalizedModule.mk m (Presentations.Module.Fractions.GradedModules.moduleDenominator a k)) ⊗ₜ[R] s = LocalizedModule.mk m 1 ⊗ₜ[R] s
  rw [LocalizedModule.smul'_mk]
  exact congrArg (fun x : Presentations.Module.Fractions.GradedModules.AwayModule a M => x ⊗ₜ[R] s) (LocalizedModule.mk_cancel (Presentations.Module.Fractions.GradedModules.moduleDenominator a k) m)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorModuleLocalization.GradedModules
