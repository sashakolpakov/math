import OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHomRestriction

/-! # Line Bundle Dual -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual

noncomputable section

/-! The actual dual module sheaf of a line bundle is a line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}}

def lineBundleDual (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X where
  sheaf := InternalHom.Construction.moduleInternalHom L.sheaf (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
  locallyTrivial x := by
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
    refine ⟨U, hx, ⟨?_⟩⟩
    exact ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app
        (InternalHom.Construction.moduleInternalHom L.sheaf (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X))).symm ≪≫
      InternalHomRestriction.Construction.moduleInternalHomRestrictIso U.ι L.sheaf (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ≪≫
      InternalHomMaps.Construction.moduleInternalHomCongr (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.sheaf) ≪≫ e)
        (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      InternalHomUnit.Construction.internalHomUnitIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme)

def lineBundleDualCongr {L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X} (e : L.sheaf ≅ M.sheaf) :
    (lineBundleDual L).sheaf ≅ (lineBundleDual M).sheaf :=
  InternalHomMaps.Construction.moduleInternalHomCongr e (Iso.refl _)

def dualLineBundleClass : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X → AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X :=
  Quotient.map lineBundleDual (fun _ _ ⟨e⟩ => ⟨lineBundleDualCongr e⟩)

def lineBundleEvaluation (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (lineBundleDual L).sheaf L.sheaf ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (lineBundleDual L).sheaf L.sheaf (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).symm
    (TensorHom.Construction.sheafBilinearUncurry (𝟙 (lineBundleDual L).sheaf))

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual
