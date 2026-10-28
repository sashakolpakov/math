import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.BinaryBiproduct
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.QuasicoherentKernels
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Module Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.ModulePullbacks

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
universe u

def modulePullbackKernelIso {X : Scheme.{u}} {M N Q : X.Modules}
    (a : M ⟶ Q) (b : N ⟶ Q) :
    kernel (biprod.desc a (-b)) ≅ pullback a b :=
  limit.isoLimitCone ⟨_, Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct a b⟩

theorem modulePullback_quasicoherent {X : Scheme.{u}} {M N Q : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Q.IsQuasicoherent]
    (a : M ⟶ Q) (b : N ⟶ Q) : (pullback a b).IsQuasicoherent := by
  have : (M ⊞ N).IsQuasicoherent := BinaryBiproduct.module_biprod_quasicoherent M N
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (modulePullbackKernelIso a b)
    (Quasicoherent.Kernels.module_quasicoherent_kernel (biprod.desc a (-b)))

theorem modulePullback_finiteType {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N Q : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    [Q.IsQuasicoherent] [M.IsFiniteType] [N.IsFiniteType]
    (a : M ⟶ Q) (b : N ⟶ Q) : (pullback a b).IsFiniteType := by
  have : (M ⊞ N).IsQuasicoherent := BinaryBiproduct.module_biprod_quasicoherent M N
  have : (M ⊞ N).IsFiniteType := BinaryBiproduct.module_biprod_finiteType M N
  have := Noetherian.QuasicoherentKernels.noetherian_quasicoherent_kernel_finiteType (biprod.desc a (-b))
  have : (kernel (biprod.desc a (-b))).IsQuasicoherent := Quasicoherent.Kernels.module_quasicoherent_kernel _
  have : (pullback a b).IsQuasicoherent := modulePullback_quasicoherent a b
  exact Quasicoherent.RestrictionFiniteType.quasicoherent_finiteType_of_iso (modulePullbackKernelIso a b)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.ModulePullbacks
