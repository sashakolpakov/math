import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CohomologyComparison
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenModule

/-! # Supported Modules -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.SupportedModules

noncomputable section

/-! Vanishing properties of the actual direct image from an open subset. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem module_restrict_isZero_of_mono
    {X : Scheme.{u}} {M N : X.Modules} (a : M ⟶ N) [Mono a]
    (U : X.Opens) (h : IsZero (N.restrict U.ι)) : IsZero (M.restrict U.ι) := by
  have : PreservesLimits (restrictFunctor U.ι) := SheafCohomology.Projective.ModuleRestrictLimits.Scheme.Modules.restrictFunctor_preservesLimits U.ι
  exact IsZero.of_mono ((restrictFunctor U.ι).map a) h

theorem openPushforward_restrict_isZero_of_intersection
    {X : Scheme.{u}} (M : X.Modules) (U W : X.Opens)
    (h : IsZero (M.restrict (U ⊓ W).ι)) :
    IsZero (((pushforward U.ι).obj (M.restrict U.ι)).restrict W.ι) := by
  have hpre := ModuleVanishingOpen.module_restrict_preimage_isZero U.ι M (U ⊓ W) h
  have he : U.ι ⁻¹ᵁ (U ⊓ W) = U.ι ⁻¹ᵁ W := by
    rw [Scheme.Hom.preimage_inf, U.ι_preimage_self, top_inf_eq]
  have hpre' : IsZero ((M.restrict U.ι).restrict (U.ι ⁻¹ᵁ W).ι) :=
    (congrArg (fun V : U.toScheme.Opens => IsZero ((M.restrict U.ι).restrict V.ι)) he).mp hpre
  exact (Quotients.FiniteDescent.OpenModule.Construction.OpenModuleBaseChange.moduleOpenBaseChangeIso U.ι W (M.restrict U.ι)).isZero_iff.mpr
    ((pushforward (U.ι ∣_ W)).map_isZero hpre')

theorem openRestrictionUnit_kernel_restrict_isZero
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    IsZero ((kernel ((restrictAdjunction U.ι).unit.app M)).restrict U.ι) := by
  have : IsIso ((restrictFunctor U.ι).map ((restrictAdjunction U.ι).unit.app M)) := inferInstance
  exact CohomologyComparison.module_kernel_restrict_isZero_of_isIso U ((restrictAdjunction U.ι).unit.app M)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.SupportedModules
