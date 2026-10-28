import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.KernelLocalizationTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.QuasicoherentCokernels

/-! # Affine Kernels -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineKernels

noncomputable section

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

def sections (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    (Spec R).Modules ⥤ ModuleCat.{u} R :=
  modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op U)

instance additive (R : CommRingCat.{u}) (U : (Spec R).Opens) : (sections R U).Additive where
  map_add := rfl

instance preservesKernel (R : CommRingCat.{u}) (U : (Spec R).Opens)
    {M N : (Spec R).Modules} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (sections R U) := by
  let E := SheafOfModules.evaluation (Spec R).ringCatSheaf (op U)
  let A := ModuleCat.restrictScalars ((Spec R).ringCatSheaf.obj.map
    ((initialOpOfTerminal isTerminalTop).to (op U))).hom
  let B := ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom
  let D := parallelPair f 0
  have hE : PreservesLimit D E := SheafOfModules.evaluationPreservesLimit D (op U)
  have hA : PreservesLimit (D ⋙ E) A := ModuleCat.preservesLimit_restrictScalars _ _
  have hB : PreservesLimit ((D ⋙ E) ⋙ A) B := ModuleCat.preservesLimit_restrictScalars _ _
  change PreservesLimit D ((E ⋙ A) ⋙ B)
  refine ⟨fun {c} hc => ⟨?_⟩⟩
  exact @isLimitOfPreserves _ _ _ _ _ _ _ B _
    (@isLimitOfPreserves _ _ _ _ _ _ _ A _
      (@isLimitOfPreserves _ _ _ _ _ _ _ E _ hc hE) hA) hB

def restriction (R : CommRingCat.{u}) (U V : (Spec R).Opens) (h : V ≤ U) :
    sections R U ⟶ sections R V where
  app M := (modulesSpecToSheaf.obj M).obj.map (homOfLE h).op
  naturality _ _ f := ((modulesSpecToSheaf.map f).hom.naturality (homOfLE h).op).symm

theorem quasicoherent {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent := by
  apply (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr
  apply (isIso_fromTildeΓ_iff_isLocalizing _).mpr
  intro r
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let τ := restriction R ⊤ U le_top
  have hM : IsLocalizedModule (.powers r) (τ.app M).hom :=
    (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance r
  have hN : IsLocalizedModule (.powers r) (τ.app N).hom :=
    (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance r
  exact KernelLocalizationTransport.isLocalized f (sections R ⊤)
    (sections R U) τ (.powers r)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineKernels
