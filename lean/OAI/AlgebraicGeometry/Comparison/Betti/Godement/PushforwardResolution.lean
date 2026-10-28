import OAI.AlgebraicGeometry.Comparison.Betti.Godement.PushforwardUnit
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Resolution
import OAI.AlgebraicGeometry.Comparison.Betti.RelativeResolutionMap

/-! # Pushforward Resolution -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.PushforwardResolution

noncomputable section

/-! A coefficient map to an actual direct image canonically induces the unit-preserving map of Godement resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {X Y : TopCat.{0}} (f : Y ⟶ X)

local instance godementDirectImageAdditive : (TopologicalSheafPullback.sheafDirectImage f).Additive :=
  TopologicalSheafPullback.sheafDirectImageAdditive f

def godementRelativeResolutionMap {A : ConstantSheafSections.ComplexSheaves X} {B : ConstantSheafSections.ComplexSheaves Y}
    (u : A ⟶ (TopologicalSheafPullback.sheafDirectImage f).obj B) :
    Resolution.godementComplex X A ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj
      (Resolution.godementComplex Y B) :=
  @RelativeResolutionMap.relativeResolutionMap _ _ _ _ _ _ (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X)
    (Functor.stalkFamilyFunctor Y) (Functor.stalkFamilyUnit Y) (TopologicalSheafPullback.sheafDirectImage f)
    (TopologicalSheafPullback.sheafDirectImageAdditive f)
    (PushforwardUnit.stalkFamilyPushforwardComparison f) (PushforwardUnit.stalkFamilyPushforwardMap_unit f) _ _ u

theorem godementRelativeResolutionMap_augmentation
    {A : ConstantSheafSections.ComplexSheaves X} {B : ConstantSheafSections.ComplexSheaves Y}
    (u : A ⟶ (TopologicalSheafPullback.sheafDirectImage f).obj B) :
    (Functor.stalkFamilyUnit X).app A ≫ (godementRelativeResolutionMap f u).f 0 =
      u ≫ (TopologicalSheafPullback.sheafDirectImage f).map ((Functor.stalkFamilyUnit Y).app B) :=
  @RelativeResolutionMap.relativeResolutionMap_augmentation _ _ _ _ _ _ (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X)
    (Functor.stalkFamilyFunctor Y) (Functor.stalkFamilyUnit Y) (TopologicalSheafPullback.sheafDirectImage f)
    (TopologicalSheafPullback.sheafDirectImageAdditive f)
    (PushforwardUnit.stalkFamilyPushforwardComparison f) (PushforwardUnit.stalkFamilyPushforwardMap_unit f) _ _ u

theorem godementRelativeResolutionMap_naturality
    {A A' : ConstantSheafSections.ComplexSheaves X} {B B' : ConstantSheafSections.ComplexSheaves Y}
    (u : A ⟶ (TopologicalSheafPullback.sheafDirectImage f).obj B)
    (u' : A' ⟶ (TopologicalSheafPullback.sheafDirectImage f).obj B') (a : A ⟶ A') (b : B ⟶ B')
    (hu : a ≫ u' = u ≫ (TopologicalSheafPullback.sheafDirectImage f).map b) :
    FunctorialResolution.resolutionMap (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X) a ≫
        godementRelativeResolutionMap f u' =
      godementRelativeResolutionMap f u ≫
        ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).map
          (FunctorialResolution.resolutionMap (Functor.stalkFamilyFunctor Y) (Functor.stalkFamilyUnit Y) b) :=
  @RelativeResolutionMap.relativeResolutionMap_naturality _ _ _ _ _ _ (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X)
    (Functor.stalkFamilyFunctor Y) (Functor.stalkFamilyUnit Y) (TopologicalSheafPullback.sheafDirectImage f)
    (TopologicalSheafPullback.sheafDirectImageAdditive f)
    (PushforwardUnit.stalkFamilyPushforwardComparison f) (PushforwardUnit.stalkFamilyPushforwardMap_unit f) _ _ _ _ u u' a b hu

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.PushforwardResolution
