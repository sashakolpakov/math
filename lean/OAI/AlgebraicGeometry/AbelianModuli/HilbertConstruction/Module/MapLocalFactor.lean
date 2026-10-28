import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapBasisExtension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers

/-! # Map Local Factor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapLocalFactor

noncomputable section

/-! Linear local factorizations through a module map that is invertible on the chosen open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {M N P : X.Modules}

def moduleMapAppEquiv (β : N ⟶ P) (U : X.Opens) [IsIso (β.app U)] :
    Γ(N, U) ≃ₗ[Γ(X, U)] Γ(P, U) :=
  LinearEquiv.ofBijective (Tensor.Powers.SheafMultilinearMap.homApp β U)
    (ConcreteCategory.bijective_of_isIso (β.app U))

def moduleMapLocalFactor (α : M ⟶ P) (β : N ⟶ P) (U : X.Opens) [IsIso (β.app U)] :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
  (moduleMapAppEquiv β U).symm.toLinearMap.comp (Tensor.Powers.SheafMultilinearMap.homApp α U)

theorem moduleMapLocalFactor_spec (α : M ⟶ P) (β : N ⟶ P) (U : X.Opens)
    [IsIso (β.app U)] (s : Γ(M, U)) :
    β.app U (moduleMapLocalFactor α β U s) = α.app U s :=
  (moduleMapAppEquiv β U).apply_symm_apply _

theorem moduleMapLocalFactor_natural (α : M ⟶ P) (β : N ⟶ P)
    {U V : X.Opens} (h : V ≤ U) [IsIso (β.app U)] [IsIso (β.app V)] (s : Γ(M, U)) :
    moduleMapLocalFactor α β V (M.presheaf.map (homOfLE h).op s) =
      N.presheaf.map (homOfLE h).op (moduleMapLocalFactor α β U s) := by
  apply (ConcreteCategory.bijective_of_isIso (β.app V)).1
  rw [moduleMapLocalFactor_spec]
  have hα := ConcreteCategory.congr_hom (α.mapPresheaf.naturality (homOfLE h).op) s
  have hβ := ConcreteCategory.congr_hom (β.mapPresheaf.naturality (homOfLE h).op)
    (moduleMapLocalFactor α β U s)
  exact hα.trans ((congrArg (fun z : Γ(P, U) => P.presheaf.map (homOfLE h).op z)
    (moduleMapLocalFactor_spec α β U s)).symm.trans hβ.symm)

theorem moduleMapLocalFactor_unique (α : M ⟶ P) (β : N ⟶ P) (U : X.Opens)
    [IsIso (β.app U)] (φ : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U))
    (hφ : ∀ s, β.app U (φ s) = α.app U s) : φ = moduleMapLocalFactor α β U := by
  apply LinearMap.ext
  intro s
  apply (ConcreteCategory.bijective_of_isIso (β.app U)).1
  exact (hφ s).trans (moduleMapLocalFactor_spec α β U s).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapLocalFactor
