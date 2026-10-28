import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ExternalTensorBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MorphismGraphFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.SectionPolynomial

/-! # Morphism Graph Bundle Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MorphismGraphBundleSections

noncomputable section

/-! Section spaces on the actual ideal-defined morphism graph are computed on its source, using the external tensor bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {R : Type u} [CommRing R] {A B : Over (Spec (.of R))}
variable [IsSeparated B.hom] [Flat A.hom] [LocallyOfFinitePresentation A.hom]

theorem morphismGraphFamilyIso_inclusion (f : A ⟶ B) :
    (MorphismGraphFamilies.morphismGraphFamilyIso f).hom.left ≫ (MorphismGraphFamilies.morphismGraphFamily f).inclusion.left = (MorphismGraphFamilies.familyGraph f).left :=
  (MorphismGraphFamilies.familyGraph f).left.toImage_imageι

def morphismGraphExternalBundle (f : A ⟶ B) (L : Line.Bundles.LineBundle A.left) (M : Line.Bundles.LineBundle B.left) :
    Line.Bundles.LineBundle (MorphismGraphFamilies.morphismGraphFamily f).scheme.left :=
  (Graph.ExternalTensorBundle.externalTensorBundle L M).pullback (MorphismGraphFamilies.morphismGraphFamily f).inclusion.left

def morphismGraphExternalBundlePullbackIso (f : A ⟶ B) (L : Line.Bundles.LineBundle A.left) (M : Line.Bundles.LineBundle B.left) :
    ((morphismGraphExternalBundle f L M).pullback (MorphismGraphFamilies.morphismGraphFamilyIso f).hom.left).sheaf ≅
      (L.tensor (M.pullback f.left)).sheaf :=
  (Scheme.Modules.pullbackComp (MorphismGraphFamilies.morphismGraphFamilyIso f).hom.left
    (MorphismGraphFamilies.morphismGraphFamily f).inclusion.left).app (Graph.ExternalTensorBundle.externalTensorBundle L M).sheaf ≪≫
      (Scheme.Modules.pullbackCongr (morphismGraphFamilyIso_inclusion f)).app (Graph.ExternalTensorBundle.externalTensorBundle L M).sheaf ≪≫
        Graph.ExternalTensorBundle.graphExternalTensorBundleIso f L M

def morphismGraphPowerSectionsIsoOfPreserves (f : A ⟶ B) (L : Line.Bundles.LineBundle A.left) (M : Line.Bundles.LineBundle B.left)
    (e : (M.pullback f.left).sheaf ≅ L.sheaf) (d : ℕ) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (MorphismGraphFamilies.morphismGraphFamily f).scheme.hom).obj
      ((morphismGraphExternalBundle f L M).tensorPower d).sheaf ≃ₗ[R]
        (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.hom).obj ((L.tensor L).tensorPower d).sheaf :=
  Intrinsic.LineBundleSections.lineBundlePowerSectionsOverIso (MorphismGraphFamilies.morphismGraphFamilyIso f) (morphismGraphExternalBundle f L M) (L.tensor L)
    (morphismGraphExternalBundlePullbackIso f L M ≪≫ Tensor.Bifunctor.tensorModuleMapIso (Iso.refl _) e) d

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MorphismGraphBundleSections
