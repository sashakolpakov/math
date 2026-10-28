import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Type Kernel Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeKernelSections

noncomputable section

/-! Kernel sections are finite on affine opens of locally Noetherian schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules Opposite

universe u

theorem affineOpen_kernel_sections_finite {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsQuasicoherent] [M.IsFiniteType]
    (f : M ⟶ N) (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(kernel f, U.1) := by
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : Module.Finite Γ(X, U.1) Γ(M, U.1) :=
    Affine.QuasicoherentFiniteTypeSections.affineOpen_quasicoherent_finiteType_sections_finite M U
  let F := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  let : F.PreservesZeroMorphisms := by
    dsimp only [F, SheafOfModules.evaluation]
    infer_instance
  let fU : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(N, U.1) := (F.map f).hom
  let eΓ : Γ(kernel f, U.1) ≃ₗ[Γ(X, U.1)] fU.ker :=
    ((PreservesKernel.iso F f).trans (ModuleCat.kernelIsoKer _)).toLinearEquiv
  have : Module.Finite Γ(X, U.1) fU.ker := inferInstance
  exact Module.Finite.equiv eΓ.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeKernelSections
