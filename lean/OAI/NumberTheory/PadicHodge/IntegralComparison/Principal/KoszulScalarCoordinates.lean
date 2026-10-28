import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.KoszulTerminalCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.ScalarAmbient

/-! # Koszul Scalar Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.KoszulScalarCoordinates

noncomputable section

/-! The scalar read from the principal Koszul comparison is precisely
the original affine oriented-purity coefficient on the same resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem cancel_scalars {C : Type*} [Category C] {S A B D E : C}
    (f : S ⟶ A) (g : A ⟶ B) (k : S ⟶ D) (e : D ≅ B) (r : D ⟶ E)
    (h : f ≫ g = k ≫ e.hom) : f ≫ (g ≫ e.inv ≫ r) = k ≫ r := by
  calc
    _ = (f ≫ g) ≫ e.inv ≫ r := by simp only [Category.assoc]
    _ = (k ≫ e.hom) ≫ e.inv ≫ r := by rw [h]
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id_assoc]

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.KoszulTerminalCoordinates
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (M : Y.Modules) [M.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(Y, U)
    (Γ(Y, U) ⧸ Koszul.OrientedTopCohomology.ideal Γ(Y, U) s))

def ambientCoordinate := KoszulPoint.ScalarAmbient.coordinate Γ(Y, U) (SectionPresheaf.rings U hU)
  (TerminalScalars.bijective U hU) s
  (KoszulTerminalCoordinates.canonicalComparison U hU N e K M ε s hreg eM)

theorem factorization :
    homologyMap (KoszulTerminalCoordinates.sourceIso U hU N K).hom c ≫ ambientCoordinate U hU N e K M ε s hreg eM =
      homologyMap (OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom c ≫
        homologyMap (DualComplexHomology.map Γ(Y, U) (KoszulTerminalCoordinates.lift U hU K M ε s hreg eM)) c ≫
          (Koszul.OrientedTopCohomology.iso Γ(Y, U) s).hom := by
  let eS := homologyMapIso
    (asIso (KoszulPartial.CanonicalMap.scalarsMap Γ(Y, U) (SectionPresheaf.rings U hU) s)) c
  have h := congrArg (fun f => homologyMap f c)
    (KoszulTerminalCoordinates.cochain_comparison U hU N e K M ε s hreg eM)
  simp only [homologyMap_comp] at h
  simpa only [ambientCoordinate, KoszulPoint.ScalarAmbient.coordinate, eS, Category.assoc]
    using cancel_scalars (homologyMap (KoszulTerminalCoordinates.sourceIso U hU N K).hom c)
    (homologyMap (AugmentedOrdered.CechForgetNaturality.ambientMap (KoszulTerminalCoordinates.canonicalComparison U hU N e K M ε s hreg eM).hom) c)
    (homologyMap (OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom c ≫
      homologyMap (DualComplexHomology.map Γ(Y, U) (KoszulTerminalCoordinates.lift U hU K M ε s hreg eM)) c)
    eS (Koszul.OrientedTopCohomology.iso Γ(Y, U) s).hom
    (by simpa only [eS, homologyMapIso_hom, asIso_hom, Category.assoc] using h)

omit [N.IsQuasicoherent] in
theorem affine_coordinate :
    homologyMap (OrientedResidueNormalizationBase.affineDualIso U hU N e K).hom c ≫
      homologyMap (DualComplexHomology.map Γ(Y, U) (KoszulTerminalCoordinates.lift U hU K M ε s hreg eM)) c ≫
        (Koszul.OrientedTopCohomology.iso Γ(Y, U) s).hom =
    homologyMap (Affine.LinearResolutionPurity.sectionComplexIso U hU N K).hom c ≫
      (LinearHomOrientedPurity.iso Γ(Y, U)
        (Koszul.OrientedTopCohomology.ideal Γ(Y, U) s) s rfl hreg
        (KoszulTerminalCoordinates.resolution U hU K M ε s eM) ((AffineOpen.InternalHom.sections U hU).obj N)
        (OrientedResidueNormalizationBase.lineIso U hU N e)).hom := by
  calc
    _ = homologyMap (KoszulTerminalCoordinates.affineMap U hU N e K M ε s hreg eM) c ≫
        (singleObjHomologySelfIso (.up ℕ) c (ModuleCat.of Γ(Y, U)
          (Γ(Y, U) ⧸ Koszul.OrientedTopCohomology.ideal Γ(Y, U) s))).hom := by
      dsimp only [KoszulTerminalCoordinates.affineMap, Koszul.NormalPurity.map]
      simp only [homologyMap_comp, Category.assoc]
      rw [Koszul.ResidueHomology.homology]
      rfl
    _ = _ := KoszulTerminalCoordinates.affine_homology U hU N e K M ε s hreg eM

variable [∀ q, ((Affine.LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]

theorem coordinate :
    (Affine.LinearResolutionPurity.sectionsHomologyIso U hU N K c).hom ≫
      homologyMap (KoszulTerminalCoordinates.sourceIso U hU N K).hom c ≫ ambientCoordinate U hU N e K M ε s hreg eM =
    (Affine.OrientedPurity.iso U hU N K M ε
      (Koszul.OrientedTopCohomology.ideal Γ(Y, U) s) eM s rfl hreg
      (OrientedResidueNormalizationBase.lineIso U hU N e)).hom := by
  rw [factorization, affine_coordinate]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.KoszulScalarCoordinates
