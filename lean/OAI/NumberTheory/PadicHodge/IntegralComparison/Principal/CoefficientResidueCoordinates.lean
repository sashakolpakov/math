import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueData
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.AffineCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleEvaluation

/-! # Coefficient Residue Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueCoordinates

noncomputable section

/-! At the unit principal open, the evaluated coefficient residue uses
exactly the affine dual of the actual augmentation-preserving lifts. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (M : Y.Modules) [M.IsQuasicoherent]
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  (T : ModuleCat.{u} Γ(Y, U)) (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ T)
  (P : ProjectiveResolution T)
  {X : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))
  (β : ModuleCat.of Γ(Y, U)
    (Γ(Y, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Y, U) s) ⟶ T)

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalization.sectionRing U
local notation "J" => OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution.normalIdeal A s
local notation "r₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOne.object U
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedKoszulResidue.target f U hU

private theorem evaluation_apply (q : ℕ) (r : SectionPresheaf.Index U)
    (φ : P.complex.X q →ₗ[A] Γ(Y, SectionPresheaf.openSubset U r))
    (x : ⋀[A]^q (Fin c → A)) :
    (show (⋀[A]^q (Fin c → A)) →ₗ[A] Γ(Y, SectionPresheaf.openSubset U r) from
      ((CoefficientResidueData.evaluation U hU T P s hreg β).f q).app (op r) φ) x =
      φ ((CoefficientResidueData.normalLift U T P s hreg β).f q x) := rfl

theorem comparison_residue_top :
    (CoefficientResidueData.map U hU N e M K ε T eM P f s hs hreg β).f c ≫
        (singleObjXSelf (.up ℕ) c Q).hom =
      (Resolution.Comparison.equivalence U hU N e M K ε T eM P).hom.f c ≫
        (CoefficientResidueData.evaluation U hU T P s hreg β).f c ≫
        Koszul.CoefficientResidue.evaluation A (SectionPresheaf.rings U hU) s Q
          (ClosedKoszulResidue.pullback f U hU s hs) := by
  have ht : (ClosedKoszulResidue.residue f U hU s hs).f c ≫
      (singleObjXSelf (.up ℕ) c Q).hom =
      Koszul.CoefficientResidue.evaluation A (SectionPresheaf.rings U hU) s Q
        (ClosedKoszulResidue.pullback f U hU s hs) :=
    Koszul.CoefficientResidue.complexMap_top A (SectionPresheaf.rings U hU) s Q
      (ClosedKoszulResidue.pullback f U hU s hs)
      (ClosedKoszulResidue.annihilated f U hU s hs)
  change ((Resolution.Comparison.equivalence U hU N e M K ε T eM P).hom ≫
    CoefficientResidueData.evaluation U hU T P s hreg β ≫ ClosedKoszulResidue.residue f U hU s hs).f c ≫
      (singleObjXSelf (.up ℕ) c Q).hom = _
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [ht]

theorem normalized_top (a : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X c) N, U)) :
    (singleObjXSelf (.up ℕ) c (ModuleCat.of A (A ⧸ J))).hom
      ((CoefficientResidueData.normalizedMap U hU N e M K ε T eM P f s hs hreg β).f c a) =
    Ideal.Quotient.mk J (e (Affine.HomEvaluation.evaluation (K.X c) N U a
      ((Affine.ChartSections.iso U hU (K.X c)).inv
        ((CoefficientResidueData.comparisonLift U hU M K ε T eM P).f c
          ((CoefficientResidueData.normalLift U T P s hreg β).f c
            (TopExteriorCoordinates.generator (Pi.basisFun A (Fin c)))))))) := by
  have hn :
      (OrientedResidueNormalizationBase.sourceAtOneIso U hU N K).hom ≫
        Mapped.SingleCoordinates.map
          (OrientedResidueNormalization.atOneFunctor U)
          (Koszul.Comparison.nativeComplex U hU N K) Q c
          (CoefficientResidueData.map U hU N e M K ε T eM P f s hs hreg β) ≫
        (single (ModuleCat A) (.up ℕ) c).map
          (OrientedResidueNormalization.targetAtOne U hU f s hs).hom =
      CoefficientResidueData.normalizedMap U hU N e M K ε T eM P f s hs hreg β := by
    simp only [Mapped.SingleCoordinates.map, CoefficientResidueData.normalizedMap, Category.assoc]
  have ha := Mapped.SingleEvaluation.map_apply A (op r₁)
    (Koszul.Comparison.nativeComplex U hU N K) Q c
    (CoefficientResidueData.map U hU N e M K ε T eM P f s hs hreg β)
    (OrientedResidueNormalizationBase.sourceAtOneIso U hU N K).hom
    (OrientedResidueNormalization.targetAtOne U hU f s hs).hom
    ((Resolution.Comparison.equivalence U hU N e M K ε T eM P).hom.f c)
    ((CoefficientResidueData.evaluation U hU T P s hreg β).f c)
    (Koszul.CoefficientResidue.evaluation A (SectionPresheaf.rings U hU) s Q
      (ClosedKoszulResidue.pullback f U hU s hs))
    (comparison_residue_top U hU N e M K ε T eM P f s hs hreg β) a
  rw [hn] at ha
  let ψ : P.complex.X c →ₗ[A] Γ(Y, SectionPresheaf.openSubset U r₁) :=
    ((Resolution.Comparison.equivalence U hU N e M K ε T eM P).hom.f c).app
      (op r₁) ((OrientedResidueNormalizationBase.sourceAtOneIso U hU N K).hom.f c a)
  let φ : (⋀[A]^c (Fin c → A)) →ₗ[A] Γ(Y, SectionPresheaf.openSubset U r₁) :=
    ((CoefficientResidueData.evaluation U hU T P s hreg β).f c).app (op r₁) ψ
  have hc := ResolutionAtOneCoordinates.comparison U hU N e M K ε T eM P c a
    ((CoefficientResidueData.normalLift U T P s hreg β).f c
      (TopExteriorCoordinates.generator (Pi.basisFun A (Fin c))))
  have hc' := (evaluation_apply U hU T P s hreg β c r₁ ψ
    (TopExteriorCoordinates.generator (Pi.basisFun A (Fin c)))).trans hc
  exact ha.trans (PrincipalResidue.AtOne.OrientedNormalization.residue_at_one U hU f s hs φ _ hc')

omit [N.IsQuasicoherent] in
theorem canonical_top (a : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X c) N, U)) :
    (singleObjXSelf (.up ℕ) c (ModuleCat.of A (A ⧸ J))).hom
      ((CoefficientResidueData.canonicalMap U hU N e M K ε T eM P s hreg β).f c a) =
    Ideal.Quotient.mk J (e (Affine.HomEvaluation.evaluation (K.X c) N U a
      ((Affine.ChartSections.iso U hU (K.X c)).inv
        ((CoefficientResidueData.comparisonLift U hU M K ε T eM P).f c
          ((CoefficientResidueData.normalLift U T P s hreg β).f c
            (TopExteriorCoordinates.generator (Pi.basisFun A (Fin c)))))))) := by
  have h : (CoefficientResidueData.canonicalMap U hU N e M K ε T eM P s hreg β).f c ≫
      (singleObjXSelf (.up ℕ) c (ModuleCat.of A (A ⧸ J))).hom =
    (OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom.f c ≫
      (DualComplexHomology.map A (CoefficientResidueData.comparisonLift U hU M K ε T eM P)).f c ≫
      (DualComplexHomology.map A (CoefficientResidueData.normalLift U T P s hreg β)).f c ≫
      Koszul.ResidueHomology.evaluation A s := by
    dsimp only [CoefficientResidueData.canonicalMap, Koszul.CoefficientNormalPurity.map, HomologicalComplex.comp_f]
    simp only [Category.assoc]
    erw [Koszul.ResidueHomology.map_top]
  have ha := ConcreteCategory.congr_hom h a
  have he := PrincipalResidue.AffineCoordinates.OrientedNormalization.affine_dual_apply U hU N e K c a
    ((Affine.ChartSections.iso U hU (K.X c)).inv
      ((CoefficientResidueData.comparisonLift U hU M K ε T eM P).f c
        ((CoefficientResidueData.normalLift U T P s hreg β).f c
          (TopExteriorCoordinates.generator (Pi.basisFun A (Fin c))))))
  rw [Iso.inv_hom_id_apply] at he
  exact ha.trans (congrArg (Ideal.Quotient.mk J) he)

theorem cochain_comparison : CoefficientResidueData.normalizedMap U hU N e M K ε T eM P f s hs hreg β =
    CoefficientResidueData.canonicalMap U hU N e M K ε T eM P s hreg β := by
  apply HomologicalComplex.to_single_hom_ext
  apply (cancel_mono (singleObjXSelf (.up ℕ) c (ModuleCat.of A (A ⧸ J))).hom).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (normalized_top U hU N e M K ε T eM P f s hs hreg β a).trans
    (canonical_top U hU N e M K ε T eM P s hreg β a).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueCoordinates
