import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackUnitSectionsTensor

/-! # Pullback Tensor Naturality -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackTensorNaturality.Construction

noncomputable section

/-! The canonical tensor comparison is natural in the scheme module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules}

def moduleGlobalSectionsMap (φ : M ⟶ N) : Γ(M, ⊤) →ₗ[Γ(Y, ⊤)] Γ(N, ⊤) :=
  φ.val.app (op ⊤) |>.hom

def moduleGlobalSectionsIso (e : M ≅ N) :
    Γ(M, ⊤) ≃ₗ[Γ(Y, ⊤)] Γ(N, ⊤) :=
  ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).mapIso e).toLinearEquiv

theorem modulePullbackSectionsTensorMap_naturality (φ : M ⟶ N) :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    (moduleGlobalSectionsMap ((Scheme.Modules.pullback f).map φ)).comp
      (PullbackSectionsTensor.Construction.modulePullbackSectionsTensorMap f M) =
    (PullbackSectionsTensor.Construction.modulePullbackSectionsTensorMap f N).comp
      ((moduleGlobalSectionsMap φ).baseChange Γ(X, ⊤)) := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a m =>
    change ((Scheme.Modules.pullback f).map φ).app ⊤
      (a • PullbackModuleSections.Construction.modulePullbackGlobalSection f M m) = a • PullbackModuleSections.Construction.modulePullbackGlobalSection f N (φ.app ⊤ m)
    rw [Scheme.Modules.Hom.app_smul, PullbackModuleSections.Construction.modulePullbackGlobalSection_naturality]

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackTensorNaturality.Construction
