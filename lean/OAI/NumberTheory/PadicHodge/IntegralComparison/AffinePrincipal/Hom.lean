import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.PrincipalComplex

/-! # Hom -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Hom.Comparison

noncomputable section

/-! The affine internal-Hom comparison respects the actual principal
restriction through the canonical tensor extension of its arguments. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomEvaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (r : Γ(X, U))

abbrev tensorFunctor := PrincipalComplex.tensorFunctor U r

def chartIso (M : X.Modules) [M.IsQuasicoherent] :
    (tensorFunctor U r).obj ((AffineOpen.InternalHom.sections U hU).obj M) ≅
      (AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj M :=
  (tensorFunctor U r).mapIso (Affine.ChartSections.iso U hU M).symm ≪≫
    (Sections.iso U hU r M).toModuleIso ≪≫
      Affine.ChartSections.iso (Sections.openSubset U r) (hU.basicOpen r) M

theorem chartIso_tmul (M : X.Modules) [M.IsQuasicoherent]
    (a : Γ(X, Sections.openSubset U r)) (m : Γ(M, U)) :
    (chartIso U hU r M).hom (a ⊗ₜ[Γ(X, U)] (Affine.ChartSections.iso U hU M).hom m) =
      (Affine.ChartSections.iso (Sections.openSubset U r) (hU.basicOpen r) M).hom
        (a • M.presheaf.map (Sections.inclusion U r).op m) := by
  change (Affine.ChartSections.iso (Sections.openSubset U r) (hU.basicOpen r) M).hom
    (Sections.iso U hU r M
      (((Affine.ChartSections.iso U hU M).inv.hom.baseChange Γ(X, Sections.openSubset U r))
        (a ⊗ₜ[Γ(X, U)] (Affine.ChartSections.iso U hU M).hom m))) = _
  rw [LinearMap.baseChange_tmul, Iso.hom_inv_id_apply, Sections.iso_tmul]

variable (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]

theorem comparison_tmul (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U))
    (a : Γ(X, Sections.openSubset U r)) (x : (AffineOpen.InternalHom.sections U hU).obj M) :
    Affine.HomEvaluation.chartEvaluation M N (Sections.openSubset U r) (hU.basicOpen r)
        ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N).presheaf.map (Sections.inclusion U r).op q)
        ((chartIso U hU r M).hom (a ⊗ₜ[Γ(X, U)] x)) =
      (chartIso U hU r N).hom (a ⊗ₜ[Γ(X, U)] Affine.HomEvaluation.chartEvaluation M N U hU q x) := by
  obtain ⟨m, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Affine.ChartSections.iso U hU M).hom).surjective x
  simp only [chartIso_tmul, Affine.HomEvaluation.chart_comparison_apply, map_smul]
  rw [Affine.HomEvaluation.restriction]

theorem comparison_square (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U)) :
    (chartIso U hU r M).hom ≫
      Affine.HomEvaluation.chartEvaluation M N (Sections.openSubset U r) (hU.basicOpen r)
        ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N).presheaf.map (Sections.inclusion U r).op q) =
    (tensorFunctor U r).map (Affine.HomEvaluation.chartEvaluation M N U hU q) ≫ (chartIso U hU r N).hom := by
  apply ConcreteCategory.hom_ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a x => exact comparison_tmul U hU r M N q a x
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Hom.Comparison
