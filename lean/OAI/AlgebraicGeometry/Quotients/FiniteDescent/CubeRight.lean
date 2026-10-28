import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeLeft

/-! # Cube Right -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRight

noncomputable section

/-! Replacement of the second cube factor and its injective pullback on
Picard groups, including compatibility with the cube coordinates. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj

universe u

namespace Construction.CubeRightFactorMap

variable {K : Type u} [Field K] (A : Over (Spec (.of K)))
variable {B C C' : Scheme.{u}} (b : B ⟶ Spec (.of K)) (c : C ⟶ Spec (.of K)) (q : C' ⟶ C)

abbrev family := ProductMap.Construction.ProductMapSquares.left c A.hom (q ≫ c) q rfl

def map : CubeProductBase.Construction.CubeProductCoordinates.total A b (q ≫ c) ⟶ CubeProductBase.Construction.CubeProductCoordinates.total A b c :=
  ProductMap.Construction.ProductMapSquares.right (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A (q ≫ c))
    (family A c q) (ProductMap.Construction.ProductMapSquares.left_second c A.hom (q ≫ c) q rfl)

theorem over_base : map A b c q ≫ CubeProductBase.Construction.CubeProductCoordinates.projection A b c = CubeProductBase.Construction.CubeProductCoordinates.projection A b (q ≫ c) := by
  change ProductMap.Construction.ProductMapSquares.right _ _ _ _ _ ≫ (_ ≫ CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) = _
  rw [← Category.assoc, ProductMap.Construction.ProductMapSquares.right_first]

def hom : CubeProductBase.Construction.CubeProductCoordinates.ambient A b (q ≫ c) ⟶ CubeProductBase.Construction.CubeProductCoordinates.ambient A b c :=
  Over.homMk (map A b c q) (by
    change map A b c q ≫ (CubeProductBase.Construction.CubeProductCoordinates.projection A b c ≫ A.hom) = CubeProductBase.Construction.CubeProductCoordinates.projection A b (q ≫ c) ≫ A.hom
    rw [← Category.assoc, over_base])

theorem first_projection : map A b c q ≫ pullback.fst (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) =
    pullback.fst (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A (q ≫ c)) := ProductMap.Construction.ProductMapSquares.right_first _ _ _ _ _

theorem second_projection : map A b c q ≫
    pullback.snd (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) ≫ pullback.fst c A.hom =
    pullback.snd (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A (q ≫ c)) ≫ pullback.fst (q ≫ c) A.hom ≫ q := by
  change ProductMap.Construction.ProductMapSquares.right _ _ _ _ _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, ProductMap.Construction.ProductMapSquares.right_second, Category.assoc, ProductMap.Construction.ProductMapSquares.left_first]

theorem cartesian : IsPullback
    (pullback.snd (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A (q ≫ c)) ≫ pullback.fst (q ≫ c) A.hom)
    (map A b c q) q
    (pullback.snd (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) ≫ pullback.fst c A.hom) :=
  (ProductMap.Construction.ProductMapSquares.right_isPullback (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A (q ≫ c))
    (family A c q) (ProductMap.Construction.ProductMapSquares.left_second c A.hom (q ≫ c) q rfl)).paste_horiz
      (ProductMap.Construction.ProductMapSquares.left_isPullback c A.hom (q ≫ c) q rfl)

theorem picard_injective [NoetherianSpace C'] (hq : ∀ U : C.Opens, IsIso (q.app U)) :
    Function.Injective (PicardPullbackId.Construction.PicardPullback.map (map A b c q)) := by
  have : Flat (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) := inferInstanceAs (Flat (pullback.snd b A.hom))
  have : Flat (pullback.snd (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c)) := inferInstance
  have : Flat (pullback.fst c A.hom) := inferInstance
  exact Picard.Construction.PicardDescent.injective (map A b c q)
    (FlatBase.Construction.FlatBaseChangeFunctions.iso q
      (pullback.snd (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) ≫ pullback.fst c A.hom)
      (pullback.snd (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A (q ≫ c)) ≫ pullback.fst (q ≫ c) A.hom)
      (map A b c q) (cartesian A b c q) hq)

variable (u : B ⟶ A.left) (hu : u ≫ A.hom = b) (v : C ⟶ A.left) (hv : v ≫ A.hom = c)

lemma first_eq : CubeRightFactorMap.hom A b c q ≫ CubeProductBase.Construction.CubeProductCoordinates.first A b c u hu = CubeProductBase.Construction.CubeProductCoordinates.first A b (q ≫ c) u hu := by
  apply Over.OverMorphism.ext
  change map A b c q ≫ (_ ≫ _ ≫ u) = _
  rw [← Category.assoc, first_projection]
  rfl

lemma second_eq : CubeRightFactorMap.hom A b c q ≫ CubeProductBase.Construction.CubeProductCoordinates.second A b c v hv =
    CubeProductBase.Construction.CubeProductCoordinates.second A b (q ≫ c) (q ≫ v) (by rw [Category.assoc, hv]) := by
  apply Over.OverMorphism.ext
  change map A b c q ≫ (_ ≫ _ ≫ v) = _
  rw [← Category.assoc _ _ v, ← Category.assoc _ _ v, second_projection]
  simp only [CubeProductBase.Construction.CubeProductCoordinates.second, Category.assoc]
  rfl

lemma third_eq : CubeRightFactorMap.hom A b c q ≫ CubeProductBase.Construction.CubeProductCoordinates.third A b c = CubeProductBase.Construction.CubeProductCoordinates.third A b (q ≫ c) :=
  Over.OverMorphism.ext (over_base A b c q)

variable [GrpObj A]

theorem cube (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    PicardPullbackId.Construction.PicardPullback.map (map A b c q)
      (CubePicardValue.Construction.CubePicardClass.cube A L (CubeProductBase.Construction.CubeProductCoordinates.first A b c u hu) (CubeProductBase.Construction.CubeProductCoordinates.second A b c v hv) (CubeProductBase.Construction.CubeProductCoordinates.third A b c)) =
    CubePicardValue.Construction.CubePicardClass.cube A L (CubeProductBase.Construction.CubeProductCoordinates.first A b (q ≫ c) u hu)
      (CubeProductBase.Construction.CubeProductCoordinates.second A b (q ≫ c) (q ≫ v) (by rw [Category.assoc, hv])) (CubeProductBase.Construction.CubeProductCoordinates.third A b (q ≫ c)) := by
  change PicardPullbackId.Construction.PicardPullback.map (CubeRightFactorMap.hom A b c q).left _ = _
  rw [CubePicardValue.Construction.CubePicardClass.pullback, first_eq, second_eq, third_eq]

end Construction.CubeRightFactorMap

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRight
