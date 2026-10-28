import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.RestrictionLimits

/-! # Isomorphism Kernel Cokernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.IsomorphismKernelCokernel

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
universe u

theorem module_kernel_restrict_isZero_of_isIso
    {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules} (a : M ⟶ N)
    [IsIso ((restrictFunctor U.ι).map a)] : IsZero ((kernel a).restrict U.ι) := by
  let F := restrictFunctor U.ι
  have : PreservesLimits F := Module.RestrictionLimits.moduleRestrictFunctor_preservesLimits U.ι
  exact (PreservesKernel.iso F a).isZero_iff.mpr (isZero_kernel_of_mono (F.map a))

theorem module_cokernel_restrict_isZero_of_isIso
    {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules} (a : M ⟶ N)
    [IsIso ((restrictFunctor U.ι).map a)] : IsZero ((cokernel a).restrict U.ι) := by
  exact (PreservesCokernel.iso (restrictFunctor U.ι) a).isZero_iff.mpr
    (isZero_cokernel_of_epi ((restrictFunctor U.ι).map a))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.IsomorphismKernelCokernel
