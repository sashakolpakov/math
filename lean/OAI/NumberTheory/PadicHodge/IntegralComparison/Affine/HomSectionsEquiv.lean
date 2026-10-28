import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomEvaluation

/-! # Hom Sections Equiv -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomSectionsEquiv

noncomputable section

/-! The literal evaluation of an internal module Hom on an affine open
is a linear equivalence for a quasicoherent source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

private def moduleHomEquiv {R : Type u} [CommRing R] (M N : ModuleCat.{v} R) :
    (M ⟶ N) ≃ₗ[R] (M →ₗ[R] N) :=
  ModuleCat.homLinearEquiv (S := R)

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (M N : X.Modules) [M.IsQuasicoherent]

def comparison : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U) ≃ₗ[Γ(X, U)]
    (Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U)) := by
  letI := AffineOpen.LinearHom.comparison_isIso U hU N (op M)
  exact (asIso ((AffineOpen.LinearHom.comparison U hU N).app (op M))).toLinearEquiv.trans
    ((moduleHomEquiv
      ((AffineOpen.InternalHom.sections U hU).obj M)
      ((AffineOpen.InternalHom.sections U hU).obj N)).trans
      (LinearEquiv.arrowCongr (ChartSections.iso U hU M).toLinearEquiv.symm
        (ChartSections.iso U hU N).toLinearEquiv.symm))

theorem comparison_apply (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U)) (m : Γ(M, U)) :
    comparison U hU M N q m = ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N U q m := by
  change (ChartSections.iso U hU N).inv
    (HomEvaluation.chartEvaluation M N U hU q
      ((ChartSections.iso U hU M).hom m)) = _
  rw [HomEvaluation.chart_comparison_apply, Iso.hom_inv_id_apply]

def equiv : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U) ≃ₗ[Γ(X, U)]
    (Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U)) :=
  LinearEquiv.ofBijective (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N U) (by
    have h : (comparison U hU M N).toLinearMap = ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N U := by
      ext q m
      exact comparison_apply U hU M N q m
    rw [← h]
    exact (comparison U hU M N).bijective)

@[simp] theorem equiv_apply (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U)) (m : Γ(M, U)) :
    equiv U hU M N q m = ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N U q m := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomSectionsEquiv
