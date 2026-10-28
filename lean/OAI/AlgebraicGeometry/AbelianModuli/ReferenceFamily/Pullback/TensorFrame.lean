import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedFrame
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackFrameComposition

/-! # Tensor Frame -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.TensorFrame

noncomputable section

/-! Canonical tensor frames of actual pullback modules, with the
proved composition law of the native monoidal pullback functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackFrameComposition

local instance tensorFrameMonoidal (X : Scheme.{0}) : MonoidalCategory X.Modules :=
  SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance tensorFramePullbackMonoidal {X Y : Scheme.{0}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal := SheafCohomology.Projective.PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f

def pullbackTensorFrame {X Y : Scheme.{0}} (f : X ⟶ Y) (M N : Y.Modules)
    (e : (Scheme.Modules.pullback f).obj M ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
    (d : (Scheme.Modules.pullback f).obj N ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) :
    (Scheme.Modules.pullback f).obj (M ⊗ N) ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X :=
  (Functor.Monoidal.μIso (Scheme.Modules.pullback f) M N).symm ≪≫
    (e ⊗ᵢ d) ≪≫ SheafCohomology.Projective.TensorSections.unitObjTensorIso X

def comparedPullbackFrame {X T U : Scheme.{0}} (f : T ⟶ X) (g : U ⟶ T) (h : U ⟶ X)
    (α : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g ≅ Scheme.Modules.pullback h)
    {M : X.Modules} (e : (Scheme.Modules.pullback f).obj M ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj T) :
    (Scheme.Modules.pullback h).obj M ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U :=
  (α.app M).symm ≪≫ RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame g e

theorem pullbackTensorFrame_comp {X T U : Scheme.{0}} (f : T ⟶ X) (g : U ⟶ T) (h : U ⟶ X)
    (α : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g ≅ Scheme.Modules.pullback h)
    [α.hom.IsMonoidal] (M N : X.Modules)
    (e : (Scheme.Modules.pullback f).obj M ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj T)
    (d : (Scheme.Modules.pullback f).obj N ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj T) :
    pullbackTensorFrame h M N (comparedPullbackFrame f g h α e) (comparedPullbackFrame f g h α d) =
      comparedPullbackFrame f g h α (pullbackTensorFrame f M N e d) :=
  SheafCohomology.Projective.PullbackFrameComposition.pullbackComp_tensorTrivialization f g h α M N e d

theorem comparedTensorFrame_eq {X T T' U : Scheme.{0}}
    (f : T ⟶ X) (g : U ⟶ T) (f' : T' ⟶ X) (g' : U ⟶ T') (h : U ⟶ X)
    (α : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g ≅ Scheme.Modules.pullback h)
    (β : Scheme.Modules.pullback f' ⋙ Scheme.Modules.pullback g' ≅ Scheme.Modules.pullback h)
    [α.hom.IsMonoidal] [β.hom.IsMonoidal] (M N : X.Modules)
    (e : (Scheme.Modules.pullback f).obj M ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj T)
    (d : (Scheme.Modules.pullback f).obj N ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj T)
    (e' : (Scheme.Modules.pullback f').obj M ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj T')
    (d' : (Scheme.Modules.pullback f').obj N ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj T')
    (he : comparedPullbackFrame f g h α e = comparedPullbackFrame f' g' h β e')
    (hd : comparedPullbackFrame f g h α d = comparedPullbackFrame f' g' h β d') :
    comparedPullbackFrame f g h α (pullbackTensorFrame f M N e d) =
      comparedPullbackFrame f' g' h β (pullbackTensorFrame f' M N e' d') :=
  (pullbackTensorFrame_comp f g h α M N e d).symm.trans
    ((congrArg₂ (pullbackTensorFrame h M N) he hd).trans
      (pullbackTensorFrame_comp f' g' h β M N e' d'))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.TensorFrame
