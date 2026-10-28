import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.QuotientSectionNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Hom
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PushforwardCoherence
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation

/-! # Quotient Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.QuotientNormalization

noncomputable section

/-! Principal restriction of the actual closed-immersion coefficient
module agrees with the literal tensor extension of its ideal quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.QuotientSectionNormalization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (U : Y.Opens) (hU : IsAffineOpen U) (r : Γ(Y, U))

def quotientLinear : (Γ(Y, U) ⧸ Closed.QuotientSectionNormalization.ideal f U hU) →ₗ[Γ(Y, U)]
    (Γ(Y, Sections.openSubset U r) ⧸ Closed.QuotientSectionNormalization.ideal f (Sections.openSubset U r) (hU.basicOpen r)) where
  toFun := Closed.QuotientSectionNormalization.quotientRestriction f U hU (Sections.openSubset U r) (hU.basicOpen r) (Sections.inclusion U r)
  map_add' := map_add _
  map_smul' a x := by
    change Closed.QuotientSectionNormalization.quotientRestriction f U hU (Sections.openSubset U r) (hU.basicOpen r) (Sections.inclusion U r)
        (Ideal.Quotient.mk (Closed.QuotientSectionNormalization.ideal f U hU) a * x) =
      Ideal.Quotient.mk (Closed.QuotientSectionNormalization.ideal f (Sections.openSubset U r) (hU.basicOpen r))
        (algebraMap Γ(Y, U) Γ(Y, Sections.openSubset U r) a) *
          Closed.QuotientSectionNormalization.quotientRestriction f U hU (Sections.openSubset U r) (hU.basicOpen r) (Sections.inclusion U r) x
    rw [map_mul]
    rfl

def tensorQuotient : Γ(Y, Sections.openSubset U r) ⊗[Γ(Y, U)] (Γ(Y, U) ⧸ Closed.QuotientSectionNormalization.ideal f U hU) →ₗ[Γ(Y, Sections.openSubset U r)]
    (Γ(Y, Sections.openSubset U r) ⧸ Closed.QuotientSectionNormalization.ideal f (Sections.openSubset U r) (hU.basicOpen r)) :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : Γ(Y, Sections.openSubset U r) →ₗ[Γ(Y, Sections.openSubset U r)] Γ(Y, Sections.openSubset U r)).smulRight
      (quotientLinear f U hU r))

omit [IsClosedImmersion f] in
theorem tensorQuotient_tmul (a : Γ(Y, Sections.openSubset U r)) (x : Γ(Y, U) ⧸ Closed.QuotientSectionNormalization.ideal f U hU) :
    tensorQuotient f U hU r (a ⊗ₜ[Γ(Y, U)] x) =
      a • Closed.QuotientSectionNormalization.quotientRestriction f U hU (Sections.openSubset U r) (hU.basicOpen r) (Sections.inclusion U r) x := rfl

local instance directImage_quasicoherent : (Closed.QuotientSectionNormalization.directImage f).IsQuasicoherent := by
  let : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  exact AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f

theorem chart_square :
    (Hom.Comparison.chartIso U hU r (Closed.QuotientSectionNormalization.directImage f)).hom ≫
        (Closed.QuotientSectionNormalization.chartIso f (Sections.openSubset U r) (hU.basicOpen r)).hom =
      (PrincipalComplex.tensorFunctor U r).map (Closed.QuotientSectionNormalization.chartIso f U hU).hom ≫
        ModuleCat.ofHom (tensorQuotient f U hU r) := by
  apply ConcreteCategory.hom_ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a x =>
    obtain ⟨m, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (Affine.ChartSections.iso U hU (Closed.QuotientSectionNormalization.directImage f)).hom).surjective x
    change (Closed.QuotientSectionNormalization.chartIso f (Sections.openSubset U r) (hU.basicOpen r)).hom
        ((Hom.Comparison.chartIso U hU r (Closed.QuotientSectionNormalization.directImage f)).hom
          (a ⊗ₜ[Γ(Y, U)] (Affine.ChartSections.iso U hU (Closed.QuotientSectionNormalization.directImage f)).hom m)) =
      tensorQuotient f U hU r (a ⊗ₜ[Γ(Y, U)]
        (Closed.QuotientSectionNormalization.chartIso f U hU).hom ((Affine.ChartSections.iso U hU (Closed.QuotientSectionNormalization.directImage f)).hom m))
    rw [Hom.Comparison.chartIso_tmul, Closed.QuotientSectionNormalization.chartIso_apply,
      tensorQuotient_tmul, Closed.QuotientSectionNormalization.chartIso_apply, map_smul,
      Closed.QuotientSectionNormalization.restriction]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.QuotientNormalization
