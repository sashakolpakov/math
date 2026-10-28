import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyTestPoints

/-! # Family Pullback Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPullbackIso

noncomputable section

/-! The actual Cartesian square of a native Hilbert family gives its
canonical scheme pullback isomorphism over every test scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def nativeFamilyPullbackIso
    {S : Scheme.{u}} (A : Over S) {T U : Over S}
    (a : U ⟶ T) (F : HilbertScheme.Presentations.Hilbert.Functor.Family A T) :
    FamilyTestPoints.nativeFamilyOver A U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily A a F) ≅
      (Over.pullback a.left).obj (FamilyTestPoints.nativeFamilyOver A T F) := by
  let H := (HilbertScheme.Presentations.Hilbert.Functor.family_isPullback A a F.val).flip
  exact Over.isoMk H.isoPullback H.isoPullback_hom_snd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPullbackIso
