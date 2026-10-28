import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionMapBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Cohomology

/-! # Coefficient Residue Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueHomology

noncomputable section

/-! The evaluated principal coefficient residue is the original
coefficient pullback in affine cohomology followed by scalar oriented purity. -/
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
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))
  (β : ModuleCat.of Γ(Y, U)
    (Γ(Y, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Y, U) s) ⟶ T)
  (Q : ProjectiveResolution (ModuleCat.of Γ(Y, U)
    (Γ(Y, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Y, U) s)))

private abbrev ambientRing : Type u := Γ(Y, U)
private abbrev lineSections : ModuleCat.{u} Γ(Y, U) := (AffineOpen.InternalHom.sections U hU).obj N
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueHomology.ambientRing U
local notation "J" => OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution.normalIdeal A s
local notation "Q₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueData.coefficientResolution U hU M K ε T eM
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueHomology.lineSections U hU N
local notation "eL" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueNormalizationBase.lineIso U hU N e
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ExactModuleDualFunctor.functor A

omit [N.IsQuasicoherent] in
theorem canonical_homology :
    homologyMap (CoefficientResidueData.canonicalMap U hU N e M K ε T eM P s hreg β) c ≫
        (singleObjHomologySelfIso (.up ℕ) c (ModuleCat.of A (A ⧸ J))).hom =
    homologyMap (Affine.LinearResolutionPurity.sectionComplexIso U hU N K).hom c ≫
      Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor A L) Q Q₀ β c ≫
        (LinearHomOrientedPurity.iso A J s rfl hreg Q L eL).hom := by
  simp only [CoefficientResidueData.canonicalMap, homologyMap_comp, Category.assoc]
  rw [Koszul.CoefficientNormalPurity.homology A s hreg Q P β]
  change homologyMap (OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom c ≫
    Resolution.CohomologyMaps.map F P Q₀ (𝟙 T) c ≫
    Resolution.CohomologyMaps.map F Q P β c ≫
    (Koszul.ResolutionOrientation.purityIso A J s rfl hreg Q).hom = _
  have hc : Resolution.CohomologyMaps.map F P Q₀ (𝟙 T) c ≫
      Resolution.CohomologyMaps.map F Q P β c =
      Resolution.CohomologyMaps.map F Q Q₀ β c := by
    simpa only [Category.comp_id] using
      (Resolution.CohomologyMaps.map_comp F Q P Q₀ β (𝟙 T) c).symm
  rw [← Category.assoc (Resolution.CohomologyMaps.map F P Q₀ (𝟙 T) c)
    (Resolution.CohomologyMaps.map F Q P β c), hc]
  have haff :
      homologyMap (OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom c =
    homologyMap (Affine.LinearResolutionPurity.sectionComplexIso U hU N K).hom c ≫
      (LinearHomDualPurity.targetHomologyIso A (Q₀).complex L eL c).hom := by
    simp only [OrientedResidueNormalizationBase.affineDualIso,
      LinearHomDualPurity.targetHomologyIso, LinearHomDualPurity.homologyIso,
      Iso.trans_hom, homologyMap_comp, homologyMapIso_hom]
    rfl
  rw [haff]
  have hf := ResolutionMapBaseChange.Linear.frame_map A Q Q₀ β L eL c
  simpa only [LinearHomOrientedPurity.iso, Iso.trans_hom, Category.assoc] using
    congrArg (fun r =>
      homologyMap (Affine.LinearResolutionPurity.sectionComplexIso U hU N K).hom c ≫ r ≫
        (Koszul.ResolutionOrientation.purityIso A J s rfl hreg Q).hom) hf.symm

variable {X : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)
  [∀ q, ((Affine.LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]

theorem normalized_homology :
    (Affine.LinearResolutionPurity.sectionsHomologyIso U hU N K c).hom ≫
      homologyMap (CoefficientResidueData.normalizedMap U hU N e M K ε T eM P f s hs hreg β) c ≫
        (singleObjHomologySelfIso (.up ℕ) c (ModuleCat.of A (A ⧸ J))).hom =
    (AffinePrincipal.Cohomology.Comparison.comparison U hU N K c).hom ≫
      Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor A L) Q Q₀ β c ≫
        (LinearHomOrientedPurity.iso A J s rfl hreg Q L eL).hom := by
  rw [CoefficientResidueCoordinates.cochain_comparison U hU N e M K ε T eM P f s hs hreg β,
    canonical_homology U hU N e M K ε T eM P s hreg β Q]
  simp only [AffinePrincipal.Cohomology.Comparison.comparison,
    Iso.trans_hom, homologyMapIso_hom, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueHomology
