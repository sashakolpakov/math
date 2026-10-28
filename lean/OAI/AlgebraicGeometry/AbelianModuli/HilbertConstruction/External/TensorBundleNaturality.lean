import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ExternalTensorBundle

/-! # Tensor Bundle Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.TensorBundleNaturality

noncomputable section

/-! External tensor bundles follow actual product morphisms and factor
bundle isomorphisms, without a restriction on the base schemes. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
variable {S : Scheme.{u}} {X Y X' Y' : Over S}

def externalTensorBundle_congr {L L' : Line.Bundles.LineBundle X.left} {M M' : Line.Bundles.LineBundle Y.left}
    (e : L.sheaf ≅ L'.sheaf) (d : M.sheaf ≅ M'.sheaf) :
    (Graph.ExternalTensorBundle.externalTensorBundle L M).sheaf ≅ (Graph.ExternalTensorBundle.externalTensorBundle L' M').sheaf :=
  Tensor.Bifunctor.tensorModuleMapIso ((Scheme.Modules.pullback (fst X Y).left).mapIso e)
    ((Scheme.Modules.pullback (snd X Y).left).mapIso d)

def externalTensorBundle_pullback_product (a : X' ⟶ X) (b : Y' ⟶ Y)
    (L : Line.Bundles.LineBundle X.left) (M : Line.Bundles.LineBundle Y.left) :
    ((Graph.ExternalTensorBundle.externalTensorBundle L M).pullback (a ⊗ₘ b).left).sheaf ≅
      (Graph.ExternalTensorBundle.externalTensorBundle (L.pullback a.left) (M.pullback b.left)).sheaf := by
  let c := (a ⊗ₘ b).left
  have ha : c ≫ (fst X Y).left = (fst X' Y').left ≫ a.left :=
    congrArg Over.Hom.left (tensorHom_fst a b)
  have hb : c ≫ (snd X Y).left = (snd X' Y').left ≫ b.left :=
    congrArg Over.Hom.left (tensorHom_snd a b)
  exact Line.Bundles.LineBundle.tensorBaseChangeIso c (L.pullback (fst X Y).left) (M.pullback (snd X Y).left) ≪≫
    Tensor.Bifunctor.tensorModuleMapIso
      ((Scheme.Modules.pullbackComp c (fst X Y).left).app L.sheaf ≪≫
        (Scheme.Modules.pullbackCongr ha).app L.sheaf ≪≫
          (Scheme.Modules.pullbackComp (fst X' Y').left a.left).symm.app L.sheaf)
      ((Scheme.Modules.pullbackComp c (snd X Y).left).app M.sheaf ≪≫
        (Scheme.Modules.pullbackCongr hb).app M.sheaf ≪≫
          (Scheme.Modules.pullbackComp (snd X' Y').left b.left).symm.app M.sheaf)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.TensorBundleNaturality
