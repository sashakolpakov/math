import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOneHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleCompositeHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SurvivorSection

/-! # Coefficient Residue Survivor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueSurvivor

noncomputable section

/-! The evaluated coefficient residue on the original surviving sheaf
has the actual affine coefficient pullback as its unit-open coordinate. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem join {C : Type*} [Category C] {S A B D E V W : C}
    (u : S ⟶ A) (i : A ⟶ B) (r : B ⟶ D) (t : D ⟶ E)
    (h : S ⟶ V) (v : V ⟶ W) (w : W ⟶ B) (m : V ⟶ E)
    (hu : u ≫ i = h ≫ v ≫ w) (hm : m = v ≫ w ≫ r ≫ t) :
    u ≫ (i ≫ r) ≫ t = h ≫ m := by
  rw [hm]
  calc
    _ = (u ≫ i) ≫ r ≫ t := by simp only [Category.assoc]
    _ = _ := by rw [hu]; simp only [Category.assoc]

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
  [∀ q, ((Affine.LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]

private abbrev ambientRing : Type u := Γ(Y, U)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueSurvivor.ambientRing U
local notation "J" => OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution.normalIdeal A s
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LinearResolutionPurity.internalComplex N K
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalization.atOneFunctor U
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedKoszulResidue.target f U hU
local notation "r₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AtOne.object U
local notation "q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueData.map U hU N e M K ε T eM P f s hs hreg β
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalizationBase.sourceAtOneIso U hU N K
local notation "t" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalization.targetAtOne U hU f s hs

def survivor : SectionPresheaf.modules U hU ((C).homology c) ⟶ D :=
  (ModuleHomology.complexIso U hU C c).inv ≫
    homologyMap q c ≫ (singleObjHomologySelfIso (.up ℕ) c D).hom

def normalizedSurvivor : (Affine.ModuleExactSections.sections U).obj ((C).homology c) ⟶
    ModuleCat.of A (A ⧸ J) :=
  ((AtOne.iso U hU).app ((C).homology c)).hom ≫
    (survivor U hU N e M K ε T eM P f s hs hreg β).app (op r₁) ≫ (t).hom

omit [∀ k, ((Affine.LinearResolutionPurity.internalComplex N K).X k).IsQuasicoherent] in
theorem evaluation_homology :
    homologyMap (CoefficientResidueData.normalizedMap U hU N e M K ε T eM P f s hs hreg β) c ≫
      (singleObjHomologySelfIso (.up ℕ) c (ModuleCat.of A (A ⧸ J))).hom =
    homologyMap (a).hom c ≫ (AtOneHomology.evaluationIso U hU C c).hom ≫
      (E).map (homologyMap q c ≫ (singleObjHomologySelfIso (.up ℕ) c D).hom) ≫ (t).hom :=
  Mapped.SingleCompositeHomology.homology_expanded E
    (Koszul.Comparison.nativeComplex U hU N K) D c q _ (a).hom _ (t).hom

theorem normalizedSurvivor_homology :
    normalizedSurvivor U hU N e M K ε T eM P f s hs hreg β =
      (Affine.LinearResolutionPurity.sectionsHomologyIso U hU N K c).hom ≫
        homologyMap (CoefficientResidueData.normalizedMap U hU N e M K ε T eM P f s hs hreg β) c ≫
          (singleObjHomologySelfIso (.up ℕ) c (ModuleCat.of A (A ⧸ J))).hom :=
  join _ _ ((E).map (homologyMap q c ≫ (singleObjHomologySelfIso (.up ℕ) c D).hom))
    (t).hom _ (homologyMap (a).hom c) _ _
    (AtOneHomology.square U hU C c)
    (evaluation_homology U hU N e M K ε T eM P f s hs hreg β)

variable (Q : ProjectiveResolution (ModuleCat.of Γ(Y, U)
  (Γ(Y, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Y, U) s)))

def sectionMap : (Affine.ModuleExactSections.sections U).obj ((C).homology c) ⟶
    (Affine.ModuleExactSections.sections U).obj (ClosedQuotient.directImage f) :=
  (AffinePrincipal.Cohomology.Comparison.comparison U hU N K c).hom ≫
    Resolution.CohomologyMaps.map
      (Resolution.CohomologyMaps.homFunctor A ((AffineOpen.InternalHom.sections U hU).obj N))
      Q (CoefficientResidueData.coefficientResolution U hU M K ε T eM) β c ≫
    (LinearHomOrientedPurity.iso A J s rfl hreg Q ((AffineOpen.InternalHom.sections U hU).obj N)
      (OrientedResidueNormalizationBase.lineIso U hU N e)).hom ≫
    (PrincipalResidue.SurvivorSection.coefficientIso U hU f s hs).inv

theorem survivor_comparison : normalizedSurvivor U hU N e M K ε T eM P f s hs hreg β =
    (AffinePrincipal.Cohomology.Comparison.comparison U hU N K c).hom ≫
      Resolution.CohomologyMaps.map
        (Resolution.CohomologyMaps.homFunctor A ((AffineOpen.InternalHom.sections U hU).obj N))
        Q (CoefficientResidueData.coefficientResolution U hU M K ε T eM) β c ≫
      (LinearHomOrientedPurity.iso A J s rfl hreg Q ((AffineOpen.InternalHom.sections U hU).obj N)
        (OrientedResidueNormalizationBase.lineIso U hU N e)).hom :=
  (normalizedSurvivor_homology U hU N e M K ε T eM P f s hs hreg β).trans
    (CoefficientResidueHomology.normalized_homology U hU N e M K ε T eM P s hreg β Q f hs)

theorem atOne :
    ((AtOne.iso U hU).app ((C).homology c)).hom ≫
      (survivor U hU N e M K ε T eM P f s hs hreg β).app (op r₁) =
    sectionMap U hU N e M K ε T eM f s hs hreg β Q ≫
      ((AtOne.iso U hU).app (ClosedQuotient.directImage f)).hom := by
  apply (cancel_mono (t).hom).mp
  calc
    _ = normalizedSurvivor U hU N e M K ε T eM P f s hs hreg β := Category.assoc _ _ _
    _ = _ := survivor_comparison U hU N e M K ε T eM P f s hs hreg β Q
    _ = _ := by
      simp only [sectionMap, PrincipalResidue.SurvivorSection.coefficientIso,
        OrientedResidueNormalization.targetAtOne,
        Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc,
        Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueSurvivor
