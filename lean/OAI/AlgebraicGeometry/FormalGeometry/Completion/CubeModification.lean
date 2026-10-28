import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductFrames
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.PicardDescent

/-! # Cube Modification -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CubeModification

noncomputable section

/-! The literal product map from two modified factors to the universal
three-factor cube, and the induced injective Picard pullback. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates

variable {K : Type u} [Field K] (A : Over (Spec (CommRingCat.of K)))
  {B C : Scheme.{u}} (p : B ⟶ A.left) (q : C ⟶ A.left)

def cubeModification : Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.ambient A (p ≫ A.hom) (q ≫ A.hom) ⟶ Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.ambient A A.hom A.hom :=
  Over.homMk (pullback.map (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.leftBase A (p ≫ A.hom)) (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.rightBase A (q ≫ A.hom))
    (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.leftBase A A.hom) (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.rightBase A A.hom)
    (PullbackCompositionMap.Construction.pullbackCompositionMap A.hom p A.hom) (PullbackCompositionMap.Construction.pullbackCompositionMap A.hom q A.hom)
    (𝟙 A.left) (by simp) (by simp)) (by
      simp [Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.projection, PullbackCompositionMap.Construction.pullbackCompositionMap])

theorem cubeModification_first : cubeModification A p q ≫
    Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.first A A.hom A.hom (𝟙 A.left) (Category.id_comp _) =
      Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.first A (p ≫ A.hom) (q ≫ A.hom) p rfl := by
  apply Over.OverMorphism.ext
  simp [cubeModification, Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.first, PullbackCompositionMap.Construction.pullbackCompositionMap]

theorem cubeModification_second : cubeModification A p q ≫
    Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.second A A.hom A.hom (𝟙 A.left) (Category.id_comp _) =
      Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.second A (p ≫ A.hom) (q ≫ A.hom) q rfl := by
  apply Over.OverMorphism.ext
  simp [cubeModification, Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.second, PullbackCompositionMap.Construction.pullbackCompositionMap]

theorem cubeModification_third : cubeModification A p q ≫ Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.third A A.hom A.hom =
    Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.third A (p ≫ A.hom) (q ≫ A.hom) := by
  apply Over.OverMorphism.ext
  simp [cubeModification, Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.third, Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.projection, PullbackCompositionMap.Construction.pullbackCompositionMap]

theorem cubeModification_picard_injective [IsProper p] [IsProper q]
    (hp : ∀ U : A.left.Opens, IsIso (p.app U))
    (hq : ∀ U : A.left.Opens, IsIso (q.app U)) :
    Function.Injective (Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (cubeModification A p q).left) := by
  have : IsProper (PullbackCompositionMap.Construction.pullbackCompositionMap A.hom p A.hom) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (PullbackCompositionMap.Construction.pullbackCompositionMap_isPullback A.hom p A.hom).flip inferInstance
  have : IsProper (PullbackCompositionMap.Construction.pullbackCompositionMap A.hom q A.hom) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (PullbackCompositionMap.Construction.pullbackCompositionMap_isPullback A.hom q A.hom).flip inferInstance
  apply FlatPicardDescent.Construction.picardPullback_injective_of_app_isIso
  intro V
  exact Product.PicardDescent.Construction.pullback_map_app_isIso (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.leftBase A A.hom) (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.rightBase A A.hom)
    (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.leftBase A (p ≫ A.hom)) (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.rightBase A (q ≫ A.hom))
    (PullbackCompositionMap.Construction.pullbackCompositionMap A.hom p A.hom) (PullbackCompositionMap.Construction.pullbackCompositionMap A.hom q A.hom)
    (by simp) (by simp)
    (FlatPicardDescent.Construction.pullbackCompositionMap_app_isIso A.hom p A.hom hp)
    (FlatPicardDescent.Construction.pullbackCompositionMap_app_isIso A.hom q A.hom hq) V

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CubeModification
