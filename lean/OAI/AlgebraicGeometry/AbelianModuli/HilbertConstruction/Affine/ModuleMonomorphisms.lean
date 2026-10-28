import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleZeroCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Kernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AssociatedPrimeScalarInjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleScalars
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Module Monomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleMonomorphisms

noncomputable section

/-! On an affine scheme, a map of quasicoherent modules is a monomorphism exactly when its actual global-section map is injective. Scalar multiplication can therefore be tested on the associated primes of the actual section module. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem module_globalSections_injective_of_mono
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    Function.Injective (f.app ⊤) := by
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
    SheafOfModules.evaluation X.ringCatSheaf (.op ⊤)
  have : PreservesFiniteLimits F :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (.op ⊤)
  have : Mono (F.map f) := by infer_instance
  exact (ModuleCat.mono_iff_injective (F.map f)).mp inferInstance

theorem affineModule_mono_iff_globalSections_injective
    {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    Mono f ↔ Function.Injective (f.app ⊤) := by
  refine ⟨fun h => @module_globalSections_injective_of_mono X M N f h, fun hf => ?_⟩
  have : (kernel f).IsQuasicoherent := Quasicoherent.Kernels.module_quasicoherent_kernel f
  have hi := module_globalSections_injective_of_mono (kernel.ι f)
  have hzero (x : Γ(kernel f, ⊤)) : x = 0 := by
    apply hi
    apply hf
    have hcomp := congrArg (fun q : kernel f ⟶ N => q.app ⊤ x) (kernel.condition f)
    change f.app ⊤ ((kernel.ι f).app ⊤ x) = 0 at hcomp
    exact hcomp.trans (by rw [map_zero, map_zero])
  have hsub : Subsingleton Γ(kernel f, ⊤) :=
    ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  have hk : IsZero (kernel f) :=
    (ModuleZeroCriterion.affineModule_isZero_iff_globalSections_subsingleton (kernel f)).mpr hsub
  exact Abelian.mono_of_kernel_ι_eq_zero f (hk.eq_of_src _ _)

theorem affineModuleScalar_mono_iff_avoids_associatedPrimes
    {X : Scheme.{u}} [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
    (M : X.Modules) [M.IsQuasicoherent] (r : Γ(X, ⊤)) :
    Mono (Global.ModuleScalars.globalModuleScalar M r) ↔
      ∀ P ∈ associatedPrimes Γ(X, ⊤) Γ(M, ⊤), r ∉ P := by
  rw [affineModule_mono_iff_globalSections_injective]
  have he : (fun x : Γ(M, ⊤) => (Global.ModuleScalars.globalModuleScalar M r).app ⊤ x) =
      (fun x : Γ(M, ⊤) => r • x) := by
    funext x
    change X.presheaf.map (𝟙 (.op (⊤ : X.Opens))) r • x = r • x
    rw [X.presheaf.map_id]
    rfl
  change Function.Injective (fun x : Γ(M, ⊤) => (Global.ModuleScalars.globalModuleScalar M r).app ⊤ x) ↔ _
  rw [he]
  exact AssociatedPrimeScalarInjectivity.scalar_injective_iff_avoids_associatedPrimes r

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleMonomorphisms
