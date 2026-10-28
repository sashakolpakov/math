import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.TerminalSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.AffineCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.NormalPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality

/-! # Koszul Terminal Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.KoszulTerminalCoordinates

noncomputable section

/-! The canonical principal Koszul comparison, at the terminal open,
is the original affine dual-resolution comparison with scalar restriction.
Thus its top coordinate uses the original oriented purity normalization. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]

def sourceIso :
    (((AffineOpen.LinearHom.sectionHom U N).mapHomologicalComplex (.up ℕ)).obj K.op) ≅
      AugmentedOrdered.CechForget.ambientComplex (Koszul.Comparison.nativeComplex U hU N K) :=
  (NatIso.mapHomologicalComplex (TerminalSections.iso U hU) (.up ℕ)).app
    (Affine.LinearResolutionPurity.internalComplex N K)

variable (M : Y.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(Y, U)
    (Γ(Y, U) ⧸ Koszul.OrientedTopCohomology.ideal Γ(Y, U) s))

abbrev resolution := Affine.OrientedPurity.resolution U hU K M ε
  (Koszul.OrientedTopCohomology.ideal Γ(Y, U) s) eM

def lift := ProjectiveResolution.lift (𝟙 _)
  (KoszulPartial.Resolution.normalResolution Γ(Y, U) s hreg)
  (resolution U hU K M ε s eM)

abbrev canonicalComparison := Koszul.Comparison.equivalence U hU N e K M ε s hreg eM

theorem comparison_apply (q : ℕ)
    (a : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X q) N, U))
    (x : ⋀[Γ(Y, U)]^q (Fin c → Γ(Y, U))) :
    (show (⋀[Γ(Y, U)]^q (Fin c → Γ(Y, U))) →ₗ[Γ(Y, U)]
        Γ(Y, SectionPresheaf.openSubset U (⊤_ (SectionPresheaf.Index U))) from
      ((canonicalComparison U hU N e K M ε s hreg eM).hom.f q).app
        (op (⊤_ (SectionPresheaf.Index U))) ((sourceIso U hU N K).hom.f q a)) x =
      algebraMap Γ(Y, U) Γ(Y, SectionPresheaf.openSubset U (⊤_ (SectionPresheaf.Index U)))
        (e (Affine.HomEvaluation.evaluation (K.X q) N U a
          ((Affine.ChartSections.iso U hU (K.X q)).inv
            ((KoszulTerminalCoordinates.lift U hU K M ε s hreg eM).f q x)))) := by
  change LineFrame.frame U hU N e (⊤_ (SectionPresheaf.Index U))
      ((show Γ(K.X q, U) →ₗ[Γ(Y, U)] Γ(N, SectionPresheaf.openSubset U (⊤_ (SectionPresheaf.Index U))) from
        (InternalHom.iso U hU (K.X q) N).hom.app (op (⊤_ (SectionPresheaf.Index U)))
          ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X q) N).presheaf.map
            (SectionPresheaf.inclusion U (⊤_ (SectionPresheaf.Index U))).op a))
        ((Affine.ChartSections.iso U hU (K.X q)).inv
          ((KoszulTerminalCoordinates.lift U hU K M ε s hreg eM).f q x))) = _
  exact OrientedResidueNormalizationBase.framed_restriction U hU N e (K.X q)
    (⊤_ (SectionPresheaf.Index U)) a _

theorem cochain_comparison :
    (sourceIso U hU N K).hom ≫ AugmentedOrdered.CechForgetNaturality.ambientMap (canonicalComparison U hU N e K M ε s hreg eM).hom =
      (OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom ≫
        DualComplexHomology.map Γ(Y, U) (KoszulTerminalCoordinates.lift U hU K M ε s hreg eM) ≫
          KoszulPartial.CanonicalMap.scalarsMap Γ(Y, U) (SectionPresheaf.rings U hU) s := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro x
  have hp := comparison_apply U hU N e K M ε s hreg eM q a x
  have ha := PrincipalResidue.AffineCoordinates.OrientedNormalization.affine_dual_apply U hU N e K q a
    ((Affine.ChartSections.iso U hU (K.X q)).inv
      ((KoszulTerminalCoordinates.lift U hU K M ε s hreg eM).f q x))
  rw [Iso.inv_hom_id_apply] at ha
  exact hp.trans (congrArg
    (algebraMap Γ(Y, U) Γ(Y, SectionPresheaf.openSubset U (⊤_ (SectionPresheaf.Index U)))) ha.symm)

def affineMap :=
  (OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom ≫
    Koszul.NormalPurity.map Γ(Y, U) s hreg (resolution U hU K M ε s eM)

omit [N.IsQuasicoherent] in
theorem affine_homology :
    homologyMap (affineMap U hU N e K M ε s hreg eM) c ≫
      (singleObjHomologySelfIso (.up ℕ) c (ModuleCat.of Γ(Y, U)
        (Γ(Y, U) ⧸ Koszul.OrientedTopCohomology.ideal Γ(Y, U) s))).hom =
    homologyMap (Affine.LinearResolutionPurity.sectionComplexIso U hU N K).hom c ≫
      (LinearHomOrientedPurity.iso Γ(Y, U)
        (Koszul.OrientedTopCohomology.ideal Γ(Y, U) s) s rfl hreg
        (resolution U hU K M ε s eM) ((AffineOpen.InternalHom.sections U hU).obj N)
        (OrientedResidueNormalizationBase.lineIso U hU N e)).hom := by
  rw [affineMap, homologyMap_comp, Category.assoc, Koszul.NormalPurity.homology]
  simp only [OrientedResidueNormalizationBase.affineDualIso,
    LinearHomOrientedPurity.iso, LinearHomDualPurity.targetHomologyIso,
    LinearHomDualPurity.homologyIso, Iso.trans_hom, homologyMap_comp,
    homologyMapIso_hom, Category.assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.KoszulTerminalCoordinates
