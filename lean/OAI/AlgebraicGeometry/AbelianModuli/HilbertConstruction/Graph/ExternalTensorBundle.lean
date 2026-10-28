import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

/-! # External Tensor Bundle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ExternalTensorBundle

noncomputable section

/-! The external product bundle restricts on the graph of a morphism to the tensor product with the pulled-back target bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}} {A B : Over S}

def externalTensorBundle (L : Line.Bundles.LineBundle A.left) (M : Line.Bundles.LineBundle B.left) : Line.Bundles.LineBundle (A ⊗ B).left :=
  (L.pullback (fst A B).left).tensor (M.pullback (snd A B).left)

def graphExternalTensorBundleIso (f : A ⟶ B) (L : Line.Bundles.LineBundle A.left) (M : Line.Bundles.LineBundle B.left) :
    ((externalTensorBundle L M).pullback (lift (𝟙 A) f).left).sheaf ≅
      (L.tensor (M.pullback f.left)).sheaf := by
  let a := (lift (𝟙 A) f).left
  have ha : a ≫ (fst A B).left = 𝟙 A.left :=
    congrArg Over.Hom.left (lift_fst (𝟙 A) f)
  have hb : a ≫ (snd A B).left = f.left :=
    congrArg Over.Hom.left (lift_snd (𝟙 A) f)
  exact Line.Bundles.LineBundle.tensorBaseChangeIso a (L.pullback (fst A B).left) (M.pullback (snd A B).left) ≪≫
    Tensor.Bifunctor.tensorModuleMapIso
      ((Scheme.Modules.pullbackComp a (fst A B).left).app L.sheaf ≪≫
        (Scheme.Modules.pullbackCongr ha).app L.sheaf ≪≫ (Scheme.Modules.pullbackId A.left).app L.sheaf)
      ((Scheme.Modules.pullbackComp a (snd A B).left).app M.sheaf ≪≫
        (Scheme.Modules.pullbackCongr hb).app M.sheaf)

def graphExternalTensorBundleIsoOfPreserves (f : A ⟶ B) (L : Line.Bundles.LineBundle A.left) (M : Line.Bundles.LineBundle B.left)
    (e : (M.pullback f.left).sheaf ≅ L.sheaf) :
    ((externalTensorBundle L M).pullback (lift (𝟙 A) f).left).sheaf ≅ (L.tensor L).sheaf :=
  graphExternalTensorBundleIso f L M ≪≫ Tensor.Bifunctor.tensorModuleMapIso (Iso.refl _) e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ExternalTensorBundle
