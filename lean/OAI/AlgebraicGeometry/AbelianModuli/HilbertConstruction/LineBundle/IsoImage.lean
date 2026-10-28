import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Iso Image -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.IsoImage

noncomputable section

/-! The direct image of a line bundle along an isomorphism is its pullback along the inverse. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

def restrictFunctorInverseIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    restrictFunctor e.inv ⋙ restrictFunctor e.hom ≅ 𝟭 X.Modules :=
  (restrictFunctorComp e.hom e.inv).symm ≪≫
    restrictFunctorCongr e.hom_inv_id ≪≫ restrictFunctorId

def lineBundlePushforwardIso_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (L : Line.Bundles.LineBundle X) :
    (pushforward f).obj L.sheaf ≅ (L.pullback (inv f)).sheaf :=
  ((restrictFunctorInverseIso (asIso f).symm).app ((pushforward f).obj L.sheaf)).symm ≪≫
    (restrictFunctor (inv f)).mapIso ((restrictFunctorAdjCounitIso f).app L.sheaf) ≪≫
      (restrictFunctorIsoPullback (inv f)).app L.sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.IsoImage
