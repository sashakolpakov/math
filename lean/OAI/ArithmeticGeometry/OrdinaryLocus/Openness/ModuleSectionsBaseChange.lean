import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackTensorNaturality

/-! # Module Sections Base Change -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSectionsBaseChange.Construction

noncomputable section

/-! The canonical tensor comparison is an isomorphism for a globally trivial line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (e : M ≅ LineBundle.Construction.structureSheafModule Y)

def trivialModuleSectionsBaseChangeEquiv :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    (Γ(X, ⊤) ⊗[Γ(Y, ⊤)] Γ(M, ⊤)) ≃ₗ[Γ(X, ⊤)]
      Γ((Scheme.Modules.pullback f).obj M, ⊤) := by
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  exact ((PullbackTensorNaturality.Construction.moduleGlobalSectionsIso e).baseChange Γ(Y, ⊤) Γ(X, ⊤) _ _).trans
    ((PullbackUnitSectionsTensor.Construction.pullbackUnitSectionsTensorEquiv f).trans
      (PullbackTensorNaturality.Construction.moduleGlobalSectionsIso ((Scheme.Modules.pullback f).mapIso e)).symm)

theorem modulePullbackSectionsTensorMap_trivial_eq :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    PullbackSectionsTensor.Construction.modulePullbackSectionsTensorMap f M = (trivialModuleSectionsBaseChangeEquiv f e).toLinearMap := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let eSource := (PullbackTensorNaturality.Construction.moduleGlobalSectionsIso e).baseChange Γ(Y, ⊤) Γ(X, ⊤) _ _
  let eTarget := PullbackTensorNaturality.Construction.moduleGlobalSectionsIso ((Scheme.Modules.pullback f).mapIso e)
  apply LinearMap.ext
  intro z
  apply eTarget.injective
  change eTarget (PullbackSectionsTensor.Construction.modulePullbackSectionsTensorMap f M z) =
    eTarget (eTarget.symm (PullbackUnitSectionsTensor.Construction.pullbackUnitSectionsTensorEquiv f (eSource z)))
  rw [LinearEquiv.apply_symm_apply]
  have hn := LinearMap.congr_fun (PullbackTensorNaturality.Construction.modulePullbackSectionsTensorMap_naturality f e.hom) z
  change eTarget (PullbackSectionsTensor.Construction.modulePullbackSectionsTensorMap f M z) =
    PullbackSectionsTensor.Construction.modulePullbackSectionsTensorMap f (LineBundle.Construction.structureSheafModule Y) (eSource z) at hn
  exact hn.trans (LinearMap.congr_fun (PullbackUnitSectionsTensor.Construction.modulePullbackSectionsTensorMap_unit_eq f) (eSource z))

include e in
theorem modulePullbackSectionsTensorMap_trivial_bijective :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Function.Bijective (PullbackSectionsTensor.Construction.modulePullbackSectionsTensorMap f M) := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  rw [modulePullbackSectionsTensorMap_trivial_eq f e]
  exact (trivialModuleSectionsBaseChangeEquiv f e).bijective

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSectionsBaseChange.Construction
