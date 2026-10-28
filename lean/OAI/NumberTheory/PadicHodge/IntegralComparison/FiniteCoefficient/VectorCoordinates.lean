import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.QuotientAction
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.RestrictionNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientPointFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.IntrinsicCoefficientHom

/-! # Vector Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.VectorCoordinates

noncomputable section

/-! Normal-equation quotient vectors and literal finite coefficient
sections define the same map from the original affine scalar module. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
attribute [local instance] Principal.OrientedResidue.structure_quasicoherent
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) (i : X ⟶ Z) [IsClosedImmersion i]
  (U : Z.Opens) (hU : IsAffineOpen U) {c : ℕ} (s : Fin c → Γ(Z, U))
  (hs : KoszulPartial.Resolution.normalIdeal Γ(Z, U) s = i.ker.ideal ⟨U, hU⟩)

include hs in
theorem quotient_apply (a : Γ(Z, U)) :
    (Principal.OrientedResidue.quotientIso i U hU s hs).hom
      ((Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage i)).hom
        (i.app U a)) = Ideal.Quotient.mk (KoszulPartial.Resolution.normalIdeal Γ(Z, U) s) a := by
  change (Ideal.quotientEquivAlgOfEq Γ(Z, U) hs.symm)
    ((Closed.QuotientSectionNormalization.chartIso i U hU).hom
      ((Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage i)).hom
        (i.app U a))) = _
  rw [Closed.QuotientSectionNormalization.chartIso_apply,
    Closed.QuotientSectionNormalization.iso_pullback, Ideal.quotientEquivAlgOfEq_mk]

theorem vector (x : Finite.FlatCoefficientSections.coefficientRing f i U) :
    letI := QuotientAction.algebra f i U hU s hs
    letI := QuotientAction.tower f i U hU s hs
    (Principal.OrientedResidue.quotientIso i U hU s hs).hom ≫
      Koszul.CoefficientPointFraction.vector Γ(Z, U) s (Finite.FlatCoefficientSections.coefficientRing f i U) x =
    (RestrictionNormalization.scalarChartIso i U hU).hom ≫
      IntegralComparison.Quotient.CoefficientEvaluation.point Γ(Z, U) (Finite.FlatCoefficientSections.quotientRing i U) (Finite.FlatCoefficientSections.coefficientRing f i U) x := by
  let := QuotientAction.algebra f i U hU s hs
  let := QuotientAction.tower f i U hU s hs
  apply (cancel_epi (Affine.ChartSections.iso U hU
    (Principal.ClosedQuotient.directImage i)).hom).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  obtain ⟨a, rfl⟩ := i.app_surjective U hU q
  change Koszul.CoefficientPointFraction.vector Γ(Z, U) s (Finite.FlatCoefficientSections.coefficientRing f i U) x
      ((Principal.OrientedResidue.quotientIso i U hU s hs).hom
        ((Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage i)).hom
          (i.app U a))) = _
  rw [quotient_apply i U hU s hs a]
  have hr : (RestrictionNormalization.scalarChartIso i U hU).hom
      ((Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage i)).hom
        (i.app U a)) = i.app U a := by
    change (Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage i)).inv
      ((Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage i)).hom
        (i.app U a)) = _
    rw [Iso.hom_inv_id_apply]
  change _ = IntegralComparison.Quotient.CoefficientEvaluation.point Γ(Z, U) (Finite.FlatCoefficientSections.quotientRing i U)
    (Finite.FlatCoefficientSections.coefficientRing f i U) x
      ((RestrictionNormalization.scalarChartIso i U hU).hom
        ((Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage i)).hom
          (i.app U a)))
  rw [hr]
  change algebraMap (Γ(Z, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Z, U) s)
      (Finite.FlatCoefficientSections.coefficientRing f i U) (Ideal.Quotient.mk _ a) * x =
    f.app (i ⁻¹ᵁ U) (i.app U a) * x
  exact congrArg (fun z => z * x) (QuotientAction.algebraMap_mk f i U hU s hs a)

omit [IsClosedImmersion i] in
 theorem coefficient (x : Finite.FlatCoefficientSections.coefficientRing f i U) :
    Affine.IntrinsicCoefficientHom.coefficientIso U hU
      (Cech.StructurePullbackUnit.coefficients f i) (Finite.FlatCoefficientSections.coefficientRing f i U)
      (Finite.FlatCoefficientSections.chartIso f i U hU) x = x := by
  change (Affine.ChartSections.iso U hU (Cech.StructurePullbackUnit.coefficients f i)).inv
    ((Affine.ChartSections.iso U hU (Cech.StructurePullbackUnit.coefficients f i)).hom x) = x
  rw [Iso.hom_inv_id_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.VectorCoordinates
