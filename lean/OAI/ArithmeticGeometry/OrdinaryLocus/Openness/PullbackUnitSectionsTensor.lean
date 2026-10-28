import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackSectionsTensor

/-! # Pullback Unit Sections Tensor -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackUnitSectionsTensor.Construction

noncomputable section

/-! The canonical tensor pullback comparison is an isomorphism for the structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def pullbackUnitSectionsTensorEquiv :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    (Γ(X, ⊤) ⊗[Γ(Y, ⊤)] Γ(LineBundle.Construction.structureSheafModule Y, ⊤)) ≃ₗ[Γ(X, ⊤)]
      Γ((Scheme.Modules.pullback f).obj (LineBundle.Construction.structureSheafModule Y), ⊤) := by
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let e : Γ((Scheme.Modules.pullback f).obj (LineBundle.Construction.structureSheafModule Y), ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
    (PullbackSectionsTensor.Construction.pullbackUnitGlobalSectionsIso f).toLinearEquiv
  exact (TensorProduct.AlgebraTensorModule.rid Γ(Y, ⊤) Γ(X, ⊤) Γ(X, ⊤)).trans
    e.symm

theorem modulePullbackSectionsTensorMap_unit_eq :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    PullbackSectionsTensor.Construction.modulePullbackSectionsTensorMap f (LineBundle.Construction.structureSheafModule Y) =
      (pullbackUnitSectionsTensorEquiv f).toLinearMap := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a r =>
    change Γ(Y, ⊤) at r
    let e : Γ((Scheme.Modules.pullback f).obj (LineBundle.Construction.structureSheafModule Y), ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
      (PullbackSectionsTensor.Construction.pullbackUnitGlobalSectionsIso f).toLinearEquiv
    apply e.injective
    change e (PullbackSectionsTensor.Construction.modulePullbackSectionsTensorMap f (LineBundle.Construction.structureSheafModule Y) (a ⊗ₜ[Γ(Y, ⊤)] r)) =
      e (e.symm (r • a))
    rw [LinearEquiv.apply_symm_apply]
    have hs : a * f.appTop r = r • a := by
      rw [Algebra.smul_def]
      exact mul_comm a (f.appTop r)
    exact (PullbackSectionsTensor.Construction.modulePullbackSectionsTensorMap_unit f a r).trans hs

theorem modulePullbackSectionsTensorMap_unit_bijective :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Function.Bijective (PullbackSectionsTensor.Construction.modulePullbackSectionsTensorMap f (LineBundle.Construction.structureSheafModule Y)) := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  rw [modulePullbackSectionsTensorMap_unit_eq]
  exact (pullbackUnitSectionsTensorEquiv f).bijective

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackUnitSectionsTensor.Construction
