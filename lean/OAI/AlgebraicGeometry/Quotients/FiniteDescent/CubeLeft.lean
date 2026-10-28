import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductBase
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductMap
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatBase
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Picard

/-! # Cube Left -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeLeft

noncomputable section

/-! Replacement of the first cube factor, its coordinate compatibility,
and injectivity on Picard groups from flat base change of functions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj

universe u

namespace Construction.CubeLeftFactorMap

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates

variable {K : Type u} [Field K] (A : Over (Spec (.of K)))
variable {B B' C : Scheme.{u}} (b : B ⟶ Spec (.of K)) (c : C ⟶ Spec (.of K)) (q : B' ⟶ B)

abbrev family := ProductMap.Construction.ProductMapSquares.left b A.hom (q ≫ b) q rfl

def map : CubeProductBase.Construction.CubeProductCoordinates.total A (q ≫ b) c ⟶ CubeProductBase.Construction.CubeProductCoordinates.total A b c :=
  ProductMap.Construction.ProductMapSquares.left (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) (CubeProductBase.Construction.CubeProductCoordinates.leftBase A (q ≫ b))
    (family A b q) (ProductMap.Construction.ProductMapSquares.left_second b A.hom (q ≫ b) q rfl)

theorem over_base : map A b c q ≫ CubeProductBase.Construction.CubeProductCoordinates.projection A b c = CubeProductBase.Construction.CubeProductCoordinates.projection A (q ≫ b) c := by
  change ProductMap.Construction.ProductMapSquares.left _ _ _ _ _ ≫ (_ ≫ CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) = _
  rw [← Category.assoc, ProductMap.Construction.ProductMapSquares.left_first, Category.assoc, ProductMap.Construction.ProductMapSquares.left_second]

def hom : CubeProductBase.Construction.CubeProductCoordinates.ambient A (q ≫ b) c ⟶ CubeProductBase.Construction.CubeProductCoordinates.ambient A b c :=
  Over.homMk (map A b c q) (by
    change map A b c q ≫ (CubeProductBase.Construction.CubeProductCoordinates.projection A b c ≫ A.hom) = CubeProductBase.Construction.CubeProductCoordinates.projection A (q ≫ b) c ≫ A.hom
    rw [← Category.assoc, over_base])

theorem first_projection : map A b c q ≫
    pullback.fst (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) ≫ pullback.fst b A.hom =
    pullback.fst (CubeProductBase.Construction.CubeProductCoordinates.leftBase A (q ≫ b)) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) ≫ pullback.fst (q ≫ b) A.hom ≫ q := by
  change ProductMap.Construction.ProductMapSquares.left _ _ _ _ _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, ProductMap.Construction.ProductMapSquares.left_first, Category.assoc, ProductMap.Construction.ProductMapSquares.left_first]

theorem second_projection : map A b c q ≫ pullback.snd (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) =
    pullback.snd (CubeProductBase.Construction.CubeProductCoordinates.leftBase A (q ≫ b)) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) :=
  ProductMap.Construction.ProductMapSquares.left_second _ _ _ _ _

theorem cartesian : IsPullback
    (pullback.fst (CubeProductBase.Construction.CubeProductCoordinates.leftBase A (q ≫ b)) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) ≫ pullback.fst (q ≫ b) A.hom)
    (map A b c q) q
    (pullback.fst (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) ≫ pullback.fst b A.hom) :=
  (ProductMap.Construction.ProductMapSquares.left_isPullback (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) (CubeProductBase.Construction.CubeProductCoordinates.leftBase A (q ≫ b))
    (family A b q) (ProductMap.Construction.ProductMapSquares.left_second b A.hom (q ≫ b) q rfl)).paste_horiz
      (ProductMap.Construction.ProductMapSquares.left_isPullback b A.hom (q ≫ b) q rfl)

theorem picard_injective [NoetherianSpace B'] (hq : ∀ U : B.Opens, IsIso (q.app U)) :
    Function.Injective (PicardPullbackId.Construction.PicardPullback.map (map A b c q)) := by
  have : Flat (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) := inferInstanceAs (Flat (pullback.snd c A.hom))
  have : Flat (pullback.fst (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c)) := inferInstance
  have : Flat (pullback.fst b A.hom) := inferInstance
  exact Picard.Construction.PicardDescent.injective (map A b c q)
    (FlatBase.Construction.FlatBaseChangeFunctions.iso q
      (pullback.fst (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) ≫ pullback.fst b A.hom)
      (pullback.fst (CubeProductBase.Construction.CubeProductCoordinates.leftBase A (q ≫ b)) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) ≫ pullback.fst (q ≫ b) A.hom)
      (map A b c q) (cartesian A b c q) hq)

variable (u : B ⟶ A.left) (hu : u ≫ A.hom = b) (v : C ⟶ A.left) (hv : v ≫ A.hom = c)

lemma first_eq : CubeLeftFactorMap.hom A b c q ≫ CubeProductBase.Construction.CubeProductCoordinates.first A b c u hu =
    CubeProductBase.Construction.CubeProductCoordinates.first A (q ≫ b) c (q ≫ u) (by rw [Category.assoc, hu]) := by
  apply Over.OverMorphism.ext
  change map A b c q ≫ (_ ≫ _ ≫ u) = _
  rw [← Category.assoc _ _ u, ← Category.assoc _ _ u, first_projection]
  simp only [CubeProductBase.Construction.CubeProductCoordinates.first, Category.assoc]
  rfl

lemma second_eq : CubeLeftFactorMap.hom A b c q ≫ CubeProductBase.Construction.CubeProductCoordinates.second A b c v hv = CubeProductBase.Construction.CubeProductCoordinates.second A (q ≫ b) c v hv := by
  apply Over.OverMorphism.ext
  change map A b c q ≫ (_ ≫ _ ≫ v) = _
  rw [← Category.assoc, second_projection]
  rfl

lemma third_eq : CubeLeftFactorMap.hom A b c q ≫ CubeProductBase.Construction.CubeProductCoordinates.third A b c = CubeProductBase.Construction.CubeProductCoordinates.third A (q ≫ b) c :=
  Over.OverMorphism.ext (over_base A b c q)

variable [GrpObj A]

theorem cube (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    PicardPullbackId.Construction.PicardPullback.map (map A b c q)
      (CubePicardValue.Construction.CubePicardClass.cube A L (CubeProductBase.Construction.CubeProductCoordinates.first A b c u hu) (CubeProductBase.Construction.CubeProductCoordinates.second A b c v hv) (CubeProductBase.Construction.CubeProductCoordinates.third A b c)) =
    CubePicardValue.Construction.CubePicardClass.cube A L (CubeProductBase.Construction.CubeProductCoordinates.first A (q ≫ b) c (q ≫ u) (by rw [Category.assoc, hu]))
      (CubeProductBase.Construction.CubeProductCoordinates.second A (q ≫ b) c v hv) (CubeProductBase.Construction.CubeProductCoordinates.third A (q ≫ b) c) := by
  change PicardPullbackId.Construction.PicardPullback.map (CubeLeftFactorMap.hom A b c q).left _ = _
  rw [CubePicardValue.Construction.CubePicardClass.pullback, first_eq, second_eq, third_eq]

end Construction.CubeLeftFactorMap

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeLeft
