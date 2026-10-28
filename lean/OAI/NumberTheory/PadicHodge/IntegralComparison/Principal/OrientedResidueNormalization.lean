import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalizationBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.NormalPurity

/-! # Oriented Residue Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalization

noncomputable section

/-! The original principal residue, evaluated at the ambient member,
and the intrinsic affine oriented-purity map use the same normalization. -/

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
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj (ClosedQuotient.directImage f))
  [QuasiIso ε] [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))

attribute [local instance] OrientedResidue.structure_quasicoherent

abbrev sectionRing : Type u := Γ(Y, U)
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalization.sectionRing U
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedQuotient.directImage f
local notation "J" => OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution.normalIdeal R s
local notation "r₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOne.object U

abbrev atOneFunctor := (evaluation (SectionPresheaf.Index U)ᵒᵖ (ModuleCat R)).obj (op r₁)

def targetAtOne : (ClosedKoszulResidue.target f U hU).obj (op r₁) ≅
    ModuleCat.of R (R ⧸ J) :=
  ((AtOne.iso U hU).app M).symm ≪≫
    Affine.ChartSections.iso U hU M ≪≫
      OrientedResidue.quotientIso f U hU s hs

theorem targetAtOne_pullback (a : R) :
    (targetAtOne U hU f s hs).hom
      (f.app (SectionPresheaf.openSubset U r₁) (algebraMap R Γ(Y, SectionPresheaf.openSubset U r₁) a)) =
        Ideal.Quotient.mk J a := by
  have ha : ((AtOne.iso U hU).app M).hom (f.app U a) =
      f.app (SectionPresheaf.openSubset U r₁) (algebraMap R Γ(Y, SectionPresheaf.openSubset U r₁) a) :=
    (ConcreteCategory.congr_hom (f.naturality (SectionPresheaf.inclusion U r₁).op) a).symm
  change (OrientedResidue.quotientIso f U hU s hs).hom
    ((Affine.ChartSections.iso U hU M).hom
      (((AtOne.iso U hU).app M).inv
        (f.app (SectionPresheaf.openSubset U r₁) (algebraMap R Γ(Y, SectionPresheaf.openSubset U r₁) a)))) = _
  rw [← ha, Iso.hom_inv_id_apply]
  change (Ideal.quotientEquivAlgOfEq R hs.symm)
    ((Closed.QuotientSectionNormalization.chartIso f U hU).hom
      ((Affine.ChartSections.iso U hU M).hom (f.app U a))) = _
  rw [Closed.QuotientSectionNormalization.chartIso_apply,
    Closed.QuotientSectionNormalization.iso_pullback, Ideal.quotientEquivAlgOfEq_mk]

abbrev coefficientResolution := Affine.OrientedPurity.resolution U hU K M ε J
  (OrientedResidue.quotientIso f U hU s hs)

def normalizedMap :
    (((AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (.up ℕ)).obj K.op) ⟶
      (single (ModuleCat R) (.up ℕ) c).obj (ModuleCat.of R (R ⧸ J)) :=
  (OrientedResidueNormalizationBase.sourceAtOneIso U hU N K).hom ≫
    ((atOneFunctor U).mapHomologicalComplex (.up ℕ)).map
      (OrientedResidue.map f U hU N e K ε s hs hreg) ≫
    (singleMapHomologicalComplex (atOneFunctor U) (.up ℕ) c).hom.app
      (ClosedKoszulResidue.target f U hU) ≫
    (single (ModuleCat R) (.up ℕ) c).map (targetAtOne U hU f s hs).hom

def canonicalMap :
    (((AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (.up ℕ)).obj K.op) ⟶
      (single (ModuleCat R) (.up ℕ) c).obj (ModuleCat.of R (R ⧸ J)) :=
  (OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom ≫
    Koszul.NormalPurity.map R s hreg (coefficientResolution U hU K f ε s hs)

omit [N.IsQuasicoherent] in
theorem canonical_homology :
    homologyMap (canonicalMap U hU N e K f ε s hs hreg) c ≫
      (singleObjHomologySelfIso (.up ℕ) c (ModuleCat.of R (R ⧸ J))).hom =
    homologyMap (Affine.LinearResolutionPurity.sectionComplexIso U hU N K).hom c ≫
      (LinearHomOrientedPurity.iso R J s rfl hreg
        (coefficientResolution U hU K f ε s hs) ((AffineOpen.InternalHom.sections U hU).obj N)
        (OrientedResidueNormalizationBase.lineIso U hU N e)).hom := by
  rw [canonicalMap, homologyMap_comp, Category.assoc, Koszul.NormalPurity.homology]
  simp only [OrientedResidueNormalizationBase.affineDualIso, LinearHomOrientedPurity.iso,
    LinearHomDualPurity.targetHomologyIso, LinearHomDualPurity.homologyIso,
    Iso.trans_hom, homologyMap_comp, homologyMapIso_hom, Category.assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalization
