import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.StructurePullbackUnit

/-! # Point Quotient Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PointQuotientSquare

noncomputable section

/-! The actual function map to a section is the canonical quotient
by concatenated normal and point parameters, including on the original
affine chart modules used by the common negative resolution. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
variable {Z X Y : Scheme.{u}} (s₀ : Z ⟶ X) (f : X ⟶ Y)
  [IsClosedImmersion f] [IsClosedImmersion (s₀ ≫ f)]
  (U : Y.Opens) (hU : IsAffineOpen U) {c m : ℕ}
  (s : Fin c → Γ(Y, U)) (t : Fin m → Γ(Y, U))
  (hs : KoszulPartial.Resolution.normalIdeal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)
  (hst : KoszulPartial.Resolution.pointIdeal Γ(Y, U) s t = (s₀ ≫ f).ker.ideal ⟨U, hU⟩)

def pointIso : Cech.StructurePullbackUnit.coefficients s₀ f ≅
    Principal.ClosedQuotient.directImage (s₀ ≫ f) :=
  (Scheme.Modules.pushforwardComp s₀ f).app (SheafOfModules.unit Z.ringCatSheaf)

def pointQuotient : (AffineOpen.InternalHom.sections U hU).obj (Cech.StructurePullbackUnit.coefficients s₀ f) ≅
    ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ KoszulPartial.Resolution.pointIdeal Γ(Y, U) s t) :=
  (AffineOpen.InternalHom.sections U hU).mapIso (pointIso s₀ f) ≪≫
    QuotientSectionNormalization.chartIso (s₀ ≫ f) U hU ≪≫
      (Ideal.quotientEquivAlgOfEq Γ(Y, U) hst.symm).toLinearEquiv.toModuleIso

omit [IsClosedImmersion f] in
theorem pointQuotient_pullback (a : Γ(Y, U)) :
    (pointQuotient s₀ f U hU s t hst).hom
      ((Affine.ChartSections.iso U hU (Cech.StructurePullbackUnit.coefficients s₀ f)).hom
        (show Γ(Cech.StructurePullbackUnit.coefficients s₀ f, U) from (s₀ ≫ f).app U a)) =
      Ideal.Quotient.mk (KoszulPartial.Resolution.pointIdeal Γ(Y, U) s t) a := by
  have h := ConcreteCategory.congr_hom
    ((AffineOpen.LinearHom.sectionsIso U hU).hom.naturality (pointIso s₀ f).hom)
    (show Γ(Cech.StructurePullbackUnit.coefficients s₀ f, U) from (s₀ ≫ f).app U a)
  change (Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage (s₀ ≫ f))).hom ((pointIso s₀ f).hom.val.app (op U) _) =
    (AffineOpen.InternalHom.sections U hU).map (pointIso s₀ f).hom ((Affine.ChartSections.iso U hU (Cech.StructurePullbackUnit.coefficients s₀ f)).hom _) at h
  change (Ideal.quotientEquivAlgOfEq Γ(Y, U) hst.symm)
    ((QuotientSectionNormalization.chartIso (s₀ ≫ f) U hU).hom
      ((AffineOpen.InternalHom.sections U hU).map (pointIso s₀ f).hom
        ((Affine.ChartSections.iso U hU (Cech.StructurePullbackUnit.coefficients s₀ f)).hom _))) = _
  rw [← h]
  change (Ideal.quotientEquivAlgOfEq Γ(Y, U) hst.symm)
    ((QuotientSectionNormalization.chartIso (s₀ ≫ f) U hU).hom
      ((Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage (s₀ ≫ f))).hom ((s₀ ≫ f).app U a))) = _
  rw [QuotientSectionNormalization.chartIso_apply,
    QuotientSectionNormalization.iso_pullback, Ideal.quotientEquivAlgOfEq_mk]

theorem square :
    (AffineOpen.InternalHom.sections U hU).map (Cech.StructurePullbackUnit.sheafMap s₀ f) ≫
      (pointQuotient s₀ f U hU s t hst).hom =
    (Principal.OrientedResidue.quotientIso f U hU s hs).hom ≫ KoszulPartial.Resolution.quotient Γ(Y, U) s t := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage f)).hom).surjective x
  obtain ⟨a, rfl⟩ := f.app_surjective U hU x
  have h := ConcreteCategory.congr_hom
    ((AffineOpen.LinearHom.sectionsIso U hU).hom.naturality
      (Cech.StructurePullbackUnit.sheafMap s₀ f)) (f.app U a)
  change (Affine.ChartSections.iso U hU (Cech.StructurePullbackUnit.coefficients s₀ f)).hom
      ((Cech.StructurePullbackUnit.sheafMap s₀ f).val.app (op U) (f.app U a)) =
    (AffineOpen.InternalHom.sections U hU).map (Cech.StructurePullbackUnit.sheafMap s₀ f)
      ((Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage f)).hom (f.app U a)) at h
  change (pointQuotient s₀ f U hU s t hst).hom
    ((AffineOpen.InternalHom.sections U hU).map (Cech.StructurePullbackUnit.sheafMap s₀ f)
      ((Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage f)).hom (f.app U a))) = _
  rw [← h]
  change (pointQuotient s₀ f U hU s t hst).hom
    ((Affine.ChartSections.iso U hU (Cech.StructurePullbackUnit.coefficients s₀ f)).hom ((s₀ ≫ f).app U a)) = _
  rw [pointQuotient_pullback]
  change _ = KoszulPartial.Resolution.quotient Γ(Y, U) s t ((Ideal.quotientEquivAlgOfEq Γ(Y, U) hs.symm)
    ((QuotientSectionNormalization.chartIso f U hU).hom
      ((Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage f)).hom (f.app U a))))
  rw [QuotientSectionNormalization.chartIso_apply,
    QuotientSectionNormalization.iso_pullback, Ideal.quotientEquivAlgOfEq_mk]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PointQuotientSquare
