import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Koszul
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedKoszulCoordinates

/-! # Product Point Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ProductPointCoordinates

noncomputable section

/-! The literal product point resolution has the original oriented
scalar coordinate, normalized in its actual point quotient. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Koszul.Comparison
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (M : Y.Modules) [M.IsQuasicoherent]
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  {c m : ℕ} (s : Fin c → Γ(Y, U)) (t : Fin m → Γ(Y, U))
  (hst : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn (Fin.append s t)))
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(Y, U)
    (Γ(Y, U) ⧸ KoszulPartial.Resolution.pointIdeal Γ(Y, U) s t))

def coordinateMap :=
  KoszulPoint.ScalarAmbient.coordinate Γ(Y, U) (SectionPresheaf.rings U hU)
      (TerminalScalars.bijective U hU) (Fin.append s t)
      (PrincipalPoint.Koszul.Comparison.productCoordinates U hU N e M K ε s t hst eM) ≫
    (Submodule.quotEquivOfEq
      (Koszul.OrientedTopCohomology.ideal Γ(Y, U) (Fin.append s t))
      (KoszulPartial.Resolution.pointIdeal Γ(Y, U) s t)
      (KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t)).toModuleIso.hom

variable [∀ q, ((Affine.LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]

def sectionIso (q : ℕ) :=
  Affine.LinearResolutionPurity.sectionsHomologyIso U hU N K q ≪≫
    homologyMapIso (KoszulTerminalCoordinates.sourceIso U hU N K) q

 theorem coordinate :
    (Affine.LinearResolutionPurity.sectionsHomologyIso U hU N K (c+m)).hom ≫
      homologyMap (KoszulTerminalCoordinates.sourceIso U hU N K).hom (c+m) ≫
        coordinateMap U hU N e M K ε s t hst eM =
    (Affine.OrientedPurity.iso U hU N K M ε
      (KoszulPartial.Resolution.pointIdeal Γ(Y, U) s t) eM
      (Fin.append s t) (KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t) hst
      (OrientedResidueNormalizationBase.lineIso U hU N e)).hom := by
  have h := KoszulPoint.ScalarAmbient.coordinate_homotopy Γ(Y, U) (SectionPresheaf.rings U hU)
    (TerminalScalars.bijective U hU) (Fin.append s t)
    (PrincipalPoint.Koszul.Comparison.productCoordinates U hU N e M K ε s t hst eM)
    (PrincipalPoint.Koszul.Comparison.fullCoordinates U hU N e M K ε s t hst eM)
    (PrincipalPoint.Koszul.Comparison.homotopy U hU N e M K ε s t hst eM)
  unfold coordinateMap
  rw [h]
  exact OrientedKoszulCoordinates.coordinate U hU N e K M ε
    (KoszulPartial.Resolution.pointIdeal Γ(Y, U) s t) eM (Fin.append s t)
    (KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t) hst

theorem coordinateMap_eq : coordinateMap U hU N e M K ε s t hst eM =
    (sectionIso U hU N K (c+m)).inv ≫
      (Affine.OrientedPurity.iso U hU N K M ε
        (KoszulPartial.Resolution.pointIdeal Γ(Y, U) s t) eM
        (Fin.append s t) (KoszulPoint.Resolution.Comparison.full_ideal Γ(Y, U) s t) hst
        (OrientedResidueNormalizationBase.lineIso U hU N e)).hom := by
  have h := coordinate U hU N e M K ε s t hst eM
  change (sectionIso U hU N K (c+m)).hom ≫ coordinateMap U hU N e M K ε s t hst eM = _ at h
  calc
    _ = (sectionIso U hU N K (c+m)).inv ≫
        ((sectionIso U hU N K (c+m)).hom ≫ coordinateMap U hU N e M K ε s t hst eM) := by
      rw [Iso.inv_hom_id_assoc]
    _ = _ := congrArg (fun a => (sectionIso U hU N K (c+m)).inv ≫ a) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ProductPointCoordinates
