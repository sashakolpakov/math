import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOne
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResidueHomology

/-! # Oriented Residue Normalization Base -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalizationBase

noncomputable section

/-! The principal normal-residue representative is normalized by the
same affine frame and canonical resolution comparison as the original
oriented local adjunction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom

variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))

theorem frame_restriction (r : SectionPresheaf.Index U) (x : Γ(N, U)) :
    LineFrame.frame U hU N e r (N.presheaf.map (SectionPresheaf.inclusion U r).op x) =
      algebraMap Γ(Y, U) Γ(Y, SectionPresheaf.openSubset U r) (e x) := by
  apply (LineFrame.frame U hU N e r).symm.injective
  rw [LinearEquiv.symm_apply_apply, LineFrame.frame_symm]
  have hx : x = e x • e.symm 1 := by
    apply e.injective
    simp only [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  calc
    N.presheaf.map (SectionPresheaf.inclusion U r).op x =
        N.presheaf.map (SectionPresheaf.inclusion U r).op (e x • e.symm 1) := congrArg _ hx
    _ = _ := N.map_smul (SectionPresheaf.inclusion U r) (e x) (e.symm 1)

theorem framed_restriction (M : Y.Modules) [M.IsQuasicoherent]
    (r : SectionPresheaf.Index U) (a : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U)) (x : Γ(M, U)) :
    LineFrame.frame U hU N e r
      ((show Γ(M, U) →ₗ[Γ(Y, U)] Γ(N, SectionPresheaf.openSubset U r) from
        (InternalHom.iso U hU M N).hom.app (op r)
          ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N).presheaf.map (SectionPresheaf.inclusion U r).op a)) x) =
      algebraMap Γ(Y, U) Γ(Y, SectionPresheaf.openSubset U r)
        (e (Affine.HomEvaluation.evaluation M N U a x)) := by
  rw [InternalHom.hom_apply, Affine.HomEvaluation.restriction,
    frame_restriction]

def scalarAtOne : Γ(Y, U) ≃ₗ[Γ(Y, U)] Γ(Y, SectionPresheaf.openSubset U (AtOne.object U)) :=
  AtOne.equiv U (SheafOfModules.unit Y.ringCatSheaf)

theorem scalarAtOne_apply (a : Γ(Y, U)) :
    scalarAtOne U a = algebraMap Γ(Y, U) Γ(Y, SectionPresheaf.openSubset U (AtOne.object U)) a := rfl

variable (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]

def sourceAtOneIso :
    (((AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (.up ℕ)).obj K.op) ≅
      (((evaluation (SectionPresheaf.Index U)ᵒᵖ (ModuleCat Γ(Y, U))).obj (op (AtOne.object U))).mapHomologicalComplex
        (.up ℕ)).obj (Koszul.Comparison.nativeComplex U hU N K) :=
  (NatIso.mapHomologicalComplex (AtOne.iso U hU) (.up ℕ)).app
    (Affine.LinearResolutionPurity.internalComplex N K)

def lineIso : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(Y, U) Γ(Y, U) :=
  (Affine.ChartSections.iso U hU N).symm ≪≫ e.toModuleIso

def affineDualIso :
    (((AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (.up ℕ)).obj K.op) ≅
      DualComplexHomology.complex Γ(Y, U)
        (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).obj K) :=
  Affine.LinearResolutionPurity.sectionComplexIso U hU N K ≪≫
    (NatIso.mapHomologicalComplex
      ((linearYoneda Γ(Y, U) (ModuleCat Γ(Y, U))).mapIso (lineIso U hU N e)) (.up ℕ)).app
        ((((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).obj K).op) ≪≫
      LinearHomDualPurity.complexIso Γ(Y, U)
        (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).obj K)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalizationBase
