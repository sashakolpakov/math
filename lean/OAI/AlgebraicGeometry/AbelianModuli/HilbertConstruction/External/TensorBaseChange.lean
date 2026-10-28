import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ExternalTensorBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterProjections

/-! # Tensor Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.TensorBaseChange

noncomputable section

/-! External tensor bundles commute with the actual product base-change map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u

def externalTensorBundle_baseChangeIso
    {S T : Scheme.{u}} (f : T ⟶ S) {A B : Over S}
    (L : Line.Bundles.LineBundle A.left) (M : Line.Bundles.LineBundle B.left) :
    ((Graph.ExternalTensorBundle.externalTensorBundle L M).pullback (Graph.FamilyNaturality.overProductBaseChangeMap f A B)).sheaf ≅
      (Graph.ExternalTensorBundle.externalTensorBundle (L.pullback (Limits.pullback.fst A.hom f))
        (M.pullback (Limits.pullback.fst B.hom f))).sheaf := by
  let c := Graph.FamilyNaturality.overProductBaseChangeMap f A B
  let A' := (Over.pullback f).obj A
  let B' := (Over.pullback f).obj B
  exact Line.Bundles.LineBundle.tensorBaseChangeIso c (L.pullback (fst A B).left) (M.pullback (snd A B).left) ≪≫
    Tensor.Bifunctor.tensorModuleMapIso
      ((Scheme.Modules.pullbackComp c (fst A B).left).app L.sheaf ≪≫
        (Scheme.Modules.pullbackCongr (Product.ParameterProjections.overProductBaseChangeMap_fst f A B)).app L.sheaf ≪≫
        (Scheme.Modules.pullbackComp (fst A' B').left (Limits.pullback.fst A.hom f)).symm.app L.sheaf)
      ((Scheme.Modules.pullbackComp c (snd A B).left).app M.sheaf ≪≫
        (Scheme.Modules.pullbackCongr (Product.ParameterProjections.overProductBaseChangeMap_snd f A B)).app M.sheaf ≪≫
        (Scheme.Modules.pullbackComp (snd A' B').left (Limits.pullback.fst B.hom f)).symm.app M.sheaf)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.TensorBaseChange
