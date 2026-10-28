import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientLifts
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Augmentation

/-! # Coefficient Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.CoefficientMaps

noncomputable section

/-! Literal coefficient restriction and augmentation normalization for
arbitrary actual affine sheaf coefficients, including finite direct images. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (r : Γ(X, U))
  (M : X.Modules) [M.IsQuasicoherent]
  (D : ModuleCat Γ(X, U)) (D' : ModuleCat Γ(X, Sections.openSubset U r))
  (e : (AffineOpen.InternalHom.sections U hU).obj M ≅ D)
  (e' : (AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj M ≅ D')

def restriction (x : D) : D' :=
  e'.hom ((Affine.ChartSections.iso (Sections.openSubset U r) (hU.basicOpen r) M).hom
    (M.presheaf.map (Sections.inclusion U r).op ((Affine.ChartSections.iso U hU M).inv (e.inv x))))

def tensorMap : (PrincipalComplex.tensorFunctor U r).obj D ⟶ D' :=
  (PrincipalComplex.tensorFunctor U r).map e.inv ≫
    (Hom.Comparison.chartIso U hU r M).hom ≫ e'.hom

theorem tensorMap_tmul (a : Γ(X, Sections.openSubset U r)) (x : D) :
    tensorMap U hU r M D D' e e' (a ⊗ₜ[Γ(X, U)] x) =
      a • restriction U hU r M D D' e e' x := by
  change e'.hom ((Hom.Comparison.chartIso U hU r M).hom
    (a ⊗ₜ[Γ(X, U)] e.inv x)) = _
  have hc := Hom.Comparison.chartIso_tmul U hU r M a
    ((Affine.ChartSections.iso U hU M).inv (e.inv x))
  have hy : (Affine.ChartSections.iso U hU M).hom
      ((Affine.ChartSections.iso U hU M).inv (e.inv x)) = e.inv x :=
    ConcreteCategory.congr_hom (Affine.ChartSections.iso U hU M).inv_hom_id _
  rw [hy] at hc
  rw [hc]
  have hs := (Affine.ChartSections.iso (Sections.openSubset U r) (hU.basicOpen r) M).hom.hom.map_smul a
    (M.presheaf.map (Sections.inclusion U r).op ((Affine.ChartSections.iso U hU M).inv (e.inv x)))
  exact (congrArg e'.hom hs).trans (e'.hom.hom.map_smul a _)

theorem square :
    (Hom.Comparison.chartIso U hU r M).hom ≫ e'.hom =
      (PrincipalComplex.tensorFunctor U r).map e.hom ≫
        tensorMap U hU r M D D' e e' := by
  simp only [tensorMap, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

variable (K : ChainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  [∀ q, Projective ((AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj (K.X q))]

theorem augmentation :
    (PrincipalComplex.chartIso U hU r (.down ℕ) K).hom.f 0 ≫
        (Affine.CoefficientLifts.resolution (Sections.openSubset U r) (hU.basicOpen r) K M ε D' e').π.f 0 =
      (PrincipalComplex.tensorFunctor U r).map
        ((Affine.CoefficientLifts.resolution U hU K M ε D e).π.f 0) ≫
        tensorMap U hU r M D D' e e' := by
  have hC : (PrincipalComplex.chartIso U hU r (.down ℕ) K).hom.f 0 =
      (Hom.Comparison.chartIso U hU r (K.X 0)).hom := rfl
  have hn := Augmentation.chart_naturality U hU r
    (show K.X 0 ⟶ M from ε.f 0)
  rw [hC, Affine.CoefficientLifts.augmentation_zero,
    Affine.CoefficientLifts.augmentation_zero, ← Category.assoc, hn,
    Category.assoc, square U hU r M D D' e e', ← Category.assoc,
    ← CategoryTheory.Functor.map_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.CoefficientMaps
