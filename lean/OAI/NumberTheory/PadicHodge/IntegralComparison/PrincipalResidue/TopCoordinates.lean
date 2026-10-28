import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.AffineCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.AtOne

/-! # Top Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.TopCoordinates.OrientedNormalization

noncomputable section

/-! The surviving component of the actual principal residue agrees
with the original affine oriented adjunction, before and after homology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom

variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  {X : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj (Principal.ClosedQuotient.directImage f))
  [QuasiIso ε] [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))

attribute [local instance] Principal.OrientedResidue.structure_quasicoherent

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalization.sectionRing U
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedQuotient.directImage f
local notation "J" => OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution.normalIdeal R s
local notation "r₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOne.object U

theorem comparison_residue_top :
    (Principal.OrientedResidue.map f U hU N e K ε s hs hreg).f c ≫
        (singleObjXSelf (.up ℕ) c (Principal.ClosedKoszulResidue.target f U hU)).hom =
      (Principal.Koszul.Comparison.equivalence U hU N e K M ε s hreg
        (Principal.OrientedResidue.quotientIso f U hU s hs)).hom.f c ≫
        Koszul.CoefficientResidue.evaluation R (Principal.SectionPresheaf.rings U hU) s
          (Principal.ClosedKoszulResidue.target f U hU)
          (Principal.ClosedKoszulResidue.pullback f U hU s hs) := by
  dsimp only [Principal.OrientedResidue.map, HomologicalComplex.comp_f]
  erw [Category.assoc, Koszul.CoefficientResidue.complexMap_top]

theorem normalized_top (a : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X c) N, U)) :
    (singleObjXSelf (.up ℕ) c (ModuleCat.of R (R ⧸ J))).hom
      ((Principal.OrientedResidueNormalization.normalizedMap U hU N e K f ε s hs hreg).f c a) =
    Ideal.Quotient.mk J (e (Affine.HomEvaluation.evaluation (K.X c) N U a
      ((Affine.ChartSections.iso U hU (K.X c)).inv
        ((AffineCoordinates.OrientedNormalization.normalLift U hU K f ε s hs hreg).f c
          (TopExteriorCoordinates.generator (Pi.basisFun R (Fin c))))))) := by
  have h := Mapped.SingleCoordinates.compose_top (Principal.OrientedResidueNormalization.atOneFunctor U)
    (Principal.Koszul.Comparison.nativeComplex U hU N K)
    (Principal.ClosedKoszulResidue.target f U hU) c
    (Principal.OrientedResidue.map f U hU N e K ε s hs hreg)
    (Principal.OrientedResidueNormalizationBase.sourceAtOneIso U hU N K).hom (Principal.OrientedResidueNormalization.targetAtOne U hU f s hs).hom
  rw [comparison_residue_top] at h
  have ha := congrArg (fun z => z.hom a) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at ha
  change (singleObjXSelf (.up ℕ) c (ModuleCat.of R (R ⧸ J))).hom
      ((Principal.OrientedResidueNormalization.normalizedMap U hU N e K f ε s hs hreg).f c a) =
    (Principal.OrientedResidueNormalization.targetAtOne U hU f s hs).hom
      ((Koszul.CoefficientResidue.evaluation R (Principal.SectionPresheaf.rings U hU) s
        (Principal.ClosedKoszulResidue.target f U hU)
        (Principal.ClosedKoszulResidue.pullback f U hU s hs)).app (op r₁)
        (((Principal.Koszul.Comparison.equivalence U hU N e K M ε s hreg
          (Principal.OrientedResidue.quotientIso f U hU s hs)).hom.f c).app (op r₁)
            ((Principal.OrientedResidueNormalizationBase.sourceAtOneIso U hU N K).hom.f c a))) at ha
  have hc := AffineCoordinates.OrientedNormalization.principal_compare_apply U hU N e K f ε s hs hreg c a
    (TopExteriorCoordinates.generator (Pi.basisFun R (Fin c)))
  exact ha.trans (AtOne.OrientedNormalization.residue_at_one U hU f s hs _ _ hc)

omit [N.IsQuasicoherent] in
theorem canonical_top (a : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X c) N, U)) :
    (singleObjXSelf (.up ℕ) c (ModuleCat.of R (R ⧸ J))).hom
      ((Principal.OrientedResidueNormalization.canonicalMap U hU N e K f ε s hs hreg).f c a) =
    Ideal.Quotient.mk J (e (Affine.HomEvaluation.evaluation (K.X c) N U a
      ((Affine.ChartSections.iso U hU (K.X c)).inv
        ((AffineCoordinates.OrientedNormalization.normalLift U hU K f ε s hs hreg).f c
          (TopExteriorCoordinates.generator (Pi.basisFun R (Fin c))))))) := by
  have h : (Principal.OrientedResidueNormalization.canonicalMap U hU N e K f ε s hs hreg).f c ≫
      (singleObjXSelf (.up ℕ) c (ModuleCat.of R (R ⧸ J))).hom =
    (Principal.OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom.f c ≫
      (DualComplexHomology.map R (AffineCoordinates.OrientedNormalization.normalLift U hU K f ε s hs hreg)).f c ≫
        Koszul.ResidueHomology.evaluation R s := by
    change ((Principal.OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom.f c ≫
      ((DualComplexHomology.map R (AffineCoordinates.OrientedNormalization.normalLift U hU K f ε s hs hreg)).f c ≫
        (Koszul.ResidueHomology.map R s).f c)) ≫ _ = _
    simp only [Category.assoc]
    erw [Koszul.ResidueHomology.map_top]
  have ha := ConcreteCategory.congr_hom h a
  have he := AffineCoordinates.OrientedNormalization.affine_dual_apply U hU N e K c a
    ((Affine.ChartSections.iso U hU (K.X c)).inv
      ((AffineCoordinates.OrientedNormalization.normalLift U hU K f ε s hs hreg).f c
        (TopExteriorCoordinates.generator (Pi.basisFun R (Fin c)))))
  rw [Iso.inv_hom_id_apply] at he
  exact ha.trans (congrArg (Ideal.Quotient.mk J) he)

theorem cochain_comparison : Principal.OrientedResidueNormalization.normalizedMap U hU N e K f ε s hs hreg =
    Principal.OrientedResidueNormalization.canonicalMap U hU N e K f ε s hs hreg := by
  apply HomologicalComplex.to_single_hom_ext
  apply (cancel_mono (singleObjXSelf (.up ℕ) c (ModuleCat.of R (R ⧸ J))).hom).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (normalized_top U hU N e K f ε s hs hreg a).trans
    (canonical_top U hU N e K f ε s hs hreg a).symm

variable [∀ q, ((Affine.LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]

theorem comparison :
    (Affine.LinearResolutionPurity.sectionsHomologyIso U hU N K c).hom ≫
      homologyMap (Principal.OrientedResidueNormalization.normalizedMap U hU N e K f ε s hs hreg) c ≫
        (singleObjHomologySelfIso (.up ℕ) c (ModuleCat.of R (R ⧸ J))).hom =
    (Affine.OrientedPurity.iso U hU N K M ε J
      (Principal.OrientedResidue.quotientIso f U hU s hs) s rfl hreg
      (Principal.OrientedResidueNormalizationBase.lineIso U hU N e)).hom := by
  rw [cochain_comparison, Principal.OrientedResidueNormalization.canonical_homology]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.TopCoordinates.OrientedNormalization
