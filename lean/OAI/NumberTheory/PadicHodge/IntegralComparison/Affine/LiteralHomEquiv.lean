import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomEvaluation

/-! # Literal Hom Equiv -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LiteralHomEquiv

noncomputable section

/-! The original local sheaf-Hom evaluation is itself a linear
equivalence on an affine open. The equivalence is normalized on the
literal section modules, without chart-coordinate ambiguity. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomEvaluation
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (M N : X.Modules) [M.IsQuasicoherent]

include hU in
theorem bijective : Function.Bijective (HomEvaluation.evaluation M N U) := by
  let eM := ChartSections.iso U hU M
  let eN := ChartSections.iso U hU N
  let f := (AffineOpen.LinearHom.comparison U hU N).app (op M)
  let : IsIso f := AffineOpen.LinearHom.comparison_isIso U hU N (op M)
  constructor
  · intro q q' h
    apply (ConcreteCategory.bijective_of_isIso f).injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨m, rfl⟩ := (ConcreteCategory.bijective_of_isIso eM.hom).surjective x
    change HomEvaluation.chartEvaluation M N U hU q (eM.hom m) = HomEvaluation.chartEvaluation M N U hU q' (eM.hom m)
    rw [HomEvaluation.chart_comparison_apply, HomEvaluation.chart_comparison_apply, h]
  · intro a
    obtain ⟨q, hq⟩ := (ConcreteCategory.bijective_of_isIso f).surjective
      (eM.inv ≫ ModuleCat.ofHom a ≫ eN.hom)
    refine ⟨q, ?_⟩
    apply LinearMap.ext
    intro m
    apply (ConcreteCategory.bijective_of_isIso eN.hom).injective
    rw [← HomEvaluation.chart_comparison_apply]
    exact (ConcreteCategory.congr_hom hq (eM.hom m)).trans (by
      change eN.hom (a (eM.inv (eM.hom m))) = _
      rw [Iso.hom_inv_id_apply])

def equiv : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U) ≃ₗ[Γ(X, U)]
    (Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U)) :=
  LinearEquiv.ofBijective (HomEvaluation.evaluation M N U) (bijective U hU M N)

theorem equiv_apply (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U)) (m : Γ(M, U)) :
    equiv U hU M N q m = HomEvaluation.evaluation M N U q m := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LiteralHomEquiv
