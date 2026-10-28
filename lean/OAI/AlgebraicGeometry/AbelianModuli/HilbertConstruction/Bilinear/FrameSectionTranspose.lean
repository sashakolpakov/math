import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.FrameCoefficientCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GlobalSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleSectionIdentity

/-! # Frame Section Transpose -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.FrameSectionTranspose

noncomputable section

/-! Pairing against reciprocal frames produces actual global sections of the original frame sheaf, linearly over any structural coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M Q : X.Modules} (F : CompatibleSheaf.CompatibleSheafFrames D.reciprocal Q)
variable (β : Sheaves.SheafBilinearMap M Q (Line.Bundles.structureModule X))

def pairingFrameSectionMap : Γ(M, ⊤) →ₗ[Γ(X, ⊤)]
    (Global.RingModulePresheaf.globalRingModulePresheaf (OpenFrame.ModuleSheaf.openFrameModuleSheaf D)).obj (.op ⊤) :=
  (OpenFrame.GlobalSections.openFrameGlobalSectionsEquiv D).symm.toLinearMap.comp
    ((FrameCoefficientTuples.pairingFrameTupleMap F β).codRestrict (OpenFrame.GlobalCompatibility.openFrameGlobalCompatibleModule D)
      (fun s => (OpenFrame.GlobalCompatibility.openFrameGlobalCompatibleModule_mem D _).mpr (FrameCoefficientCompatibility.pairingFrameTuple_compatible F β s)))

theorem pairingFrameSectionMap_tuple (s : Γ(M, ⊤)) :
    (OpenFrame.GlobalSections.openFrameGlobalSectionsEquiv D (pairingFrameSectionMap F β s)).val = FrameCoefficientTuples.pairingFrameTupleMap F β s :=
  congrArg Subtype.val ((OpenFrame.GlobalSections.openFrameGlobalSectionsEquiv D).apply_symm_apply _)

def coefficientPairingFrameSectionMap {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤)) :
    (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M →ₗ[R]
      (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj (OpenFrame.ModuleSheaf.openFrameModuleSheaf D) :=
  ((ModuleCat.restrictScalars c).map (ModuleCat.ofHom (pairingFrameSectionMap F β))).hom.comp
    (Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso c M).toLinearMap

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.FrameSectionTranspose
