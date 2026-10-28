import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.KoszulScalarCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Resolution

/-! # Oriented Koszul Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedKoszulCoordinates

noncomputable section

/-! Oriented principal Koszul coordinates for a fixed quotient ideal.
The quotient need not be named by the chosen equations, so different
parameter tuples act on the same original affine cohomology group. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem cancel_scalars {C : Type*} [Category C] {S A B D E : C}
    (f : S ⟶ A) (g : A ⟶ B) (k : S ⟶ D) (e : D ≅ B) (r : D ⟶ E)
    (h : f ≫ g = k ≫ e.hom) : f ≫ (g ≫ e.inv ≫ r) = k ≫ r := by
  rw [← Category.assoc f g, h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (M : Y.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  (I : Ideal Γ(Y, U))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ I))
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = I)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))

abbrev resolution := Affine.OrientedPurity.resolution U hU K M ε I eM

abbrev comparison :=
  (Resolution.Comparison.equivalence U hU N e M K ε _ eM
    (Koszul.ResolutionOrientation.resolutionAtIdeal Γ(Y, U) I s hs hreg)).trans
      (HomotopyEquiv.ofIso (Koszul.HomCoefficientComplex.iso Γ(Y, U)
        (Fin c → Γ(Y, U)) (LineFrame.scalars U hU)
        (Koszul.GeneratorMatrix.equation Γ(Y, U) s)))

abbrev lift := ProjectiveResolution.lift (𝟙 _)
  (Koszul.ResolutionOrientation.resolutionAtIdeal Γ(Y, U) I s hs hreg)
  (resolution U hU K M ε I eM)

 theorem cochain_comparison :
    (KoszulTerminalCoordinates.sourceIso U hU N K).hom ≫
      AugmentedOrdered.CechForgetNaturality.ambientMap (comparison U hU N e K M ε I eM s hs hreg).hom =
    (OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom ≫
      DualComplexHomology.map Γ(Y, U) (OrientedKoszulCoordinates.lift U hU K M ε I eM s hs hreg) ≫
        KoszulPartial.CanonicalMap.scalarsMap Γ(Y, U) (SectionPresheaf.rings U hU) s := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro x
  have hp := OrientedResidueNormalizationBase.framed_restriction U hU N e (K.X q)
    (⊤_ (SectionPresheaf.Index U)) a
    ((Affine.ChartSections.iso U hU (K.X q)).inv
      ((OrientedKoszulCoordinates.lift U hU K M ε I eM s hs hreg).f q x))
  have ha := PrincipalResidue.AffineCoordinates.OrientedNormalization.affine_dual_apply U hU N e K q a
    ((Affine.ChartSections.iso U hU (K.X q)).inv
      ((OrientedKoszulCoordinates.lift U hU K M ε I eM s hs hreg).f q x))
  rw [Iso.inv_hom_id_apply] at ha
  exact hp.trans (congrArg
    (algebraMap Γ(Y, U) Γ(Y, SectionPresheaf.openSubset U (⊤_ (SectionPresheaf.Index U)))) ha.symm)

abbrev ambientCoordinate := KoszulPoint.ScalarAmbient.coordinate Γ(Y, U) (SectionPresheaf.rings U hU)
  (TerminalScalars.bijective U hU) s
  (comparison U hU N e K M ε I eM s hs hreg)

 theorem factorization :
    homologyMap (KoszulTerminalCoordinates.sourceIso U hU N K).hom c ≫
      ambientCoordinate U hU N e K M ε I eM s hs hreg =
    homologyMap (OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom c ≫
      homologyMap (DualComplexHomology.map Γ(Y, U) (OrientedKoszulCoordinates.lift U hU K M ε I eM s hs hreg)) c ≫
        (Koszul.OrientedTopCohomology.iso Γ(Y, U) s).hom := by
  let eS := homologyMapIso
    (asIso (KoszulPartial.CanonicalMap.scalarsMap Γ(Y, U) (SectionPresheaf.rings U hU) s)) c
  have h := congrArg (fun f => homologyMap f c)
    (cochain_comparison U hU N e K M ε I eM s hs hreg)
  simp only [homologyMap_comp] at h
  simpa only [ambientCoordinate, KoszulPoint.ScalarAmbient.coordinate, eS, Category.assoc]
    using cancel_scalars (homologyMap (KoszulTerminalCoordinates.sourceIso U hU N K).hom c)
      (homologyMap (AugmentedOrdered.CechForgetNaturality.ambientMap (comparison U hU N e K M ε I eM s hs hreg).hom) c)
      (homologyMap (OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom c ≫
        homologyMap (DualComplexHomology.map Γ(Y, U) (OrientedKoszulCoordinates.lift U hU K M ε I eM s hs hreg)) c)
      eS (Koszul.OrientedTopCohomology.iso Γ(Y, U) s).hom
      (by simpa only [eS, homologyMapIso_hom, asIso_hom, Category.assoc] using h)

variable [∀ q, ((Affine.LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]

 theorem coordinate :
    (Affine.LinearResolutionPurity.sectionsHomologyIso U hU N K c).hom ≫
      homologyMap (KoszulTerminalCoordinates.sourceIso U hU N K).hom c ≫
      ambientCoordinate U hU N e K M ε I eM s hs hreg ≫
        (Submodule.quotEquivOfEq (Koszul.OrientedTopCohomology.ideal Γ(Y, U) s) I hs).toModuleIso.hom =
    (Affine.OrientedPurity.iso U hU N K M ε I eM s hs hreg
      (OrientedResidueNormalizationBase.lineIso U hU N e)).hom := by
  rw [← Category.assoc (homologyMap (KoszulTerminalCoordinates.sourceIso U hU N K).hom c),
    factorization]
  simp only [Affine.OrientedPurity.iso, OrientedResidueNormalizationBase.affineDualIso,
    LinearHomOrientedPurity.iso, LinearHomDualPurity.targetHomologyIso,
    LinearHomDualPurity.homologyIso, Koszul.ResolutionOrientation.purityIso,
    Koszul.DeterminantTransition.isoToIdeal, Iso.trans_hom,
    homologyMap_comp, homologyMapIso_hom, Category.assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedKoszulCoordinates
