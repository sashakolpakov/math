import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! # Representable Triple Cycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.RepresentableTripleCycle

noncomputable section

/-! Explicit cyclic transition maps on triple intersections of representable relative charts. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open Functor.relativelyRepresentable
universe u

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
variable {ι : Type u} {X : ι → Over S} {f : ∀ i, yoneda.obj (X i) ⟶ F}
variable (h : ∀ i, yoneda.relativelyRepresentable (f i))

def relativeRepresentableTripleCycle (i j k : ι) :
    (h i).pullback₃ (f j) (f k) ⟶ (h j).pullback₃ (f k) (f i) :=
  lift₃ (h j) (f k) (f i)
    (pullback₃.p₂ (h i) (f j) (f k)) (pullback₃.p₃ (h i) (f j) (f k))
    (pullback₃.p₁ (h i) (f j) (f k))
    ((pullback₃.map_p₂_comp (h i) (f j) (f k)).trans (pullback₃.map_p₃_comp (h i) (f j) (f k)).symm)
    ((pullback₃.map_p₂_comp (h i) (f j) (f k)).trans (pullback₃.map_p₁_comp (h i) (f j) (f k)).symm)

theorem relativeRepresentableTripleCycle_p₁ (i j k : ι) :
    relativeRepresentableTripleCycle h i j k ≫ pullback₃.p₁ (h j) (f k) (f i) =
      pullback₃.p₂ (h i) (f j) (f k) := lift₃_p₁ (h j) (f k) (f i) _ _ _ _ _

theorem relativeRepresentableTripleCycle_p₂ (i j k : ι) :
    relativeRepresentableTripleCycle h i j k ≫ pullback₃.p₂ (h j) (f k) (f i) =
      pullback₃.p₃ (h i) (f j) (f k) := lift₃_p₂ (h j) (f k) (f i) _ _ _ _ _

theorem relativeRepresentableTripleCycle_p₃ (i j k : ι) :
    relativeRepresentableTripleCycle h i j k ≫ pullback₃.p₃ (h j) (f k) (f i) =
      pullback₃.p₁ (h i) (f j) (f k) := lift₃_p₃ (h j) (f k) (f i) _ _ _ _ _

theorem threeMap_projection_recovery {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ A) (p : A ⟶ E) (q : D ⟶ E) (r : B ⟶ E)
    (hc : c ≫ p = q) (hb : b ≫ q = r) (ha : a ≫ r = p) :
    (a ≫ b ≫ c) ≫ p = 𝟙 A ≫ p := by
  rw [Category.assoc, Category.assoc, hc, hb, ha, Category.id_comp]

theorem relativeRepresentableTripleCycle_cocycle (i j k : ι) :
    relativeRepresentableTripleCycle h i j k ≫ relativeRepresentableTripleCycle h j k i ≫
      relativeRepresentableTripleCycle h k i j = 𝟙 _ := by
  apply pullback₃.hom_ext
  · exact threeMap_projection_recovery _ _ _ _ _ _
      (relativeRepresentableTripleCycle_p₁ h k i j)
      (relativeRepresentableTripleCycle_p₂ h j k i)
      (relativeRepresentableTripleCycle_p₃ h i j k)
  · exact threeMap_projection_recovery _ _ _ _ _ _
      (relativeRepresentableTripleCycle_p₂ h k i j)
      (relativeRepresentableTripleCycle_p₃ h j k i)
      (relativeRepresentableTripleCycle_p₁ h i j k)
  · exact threeMap_projection_recovery _ _ _ _ _ _
      (relativeRepresentableTripleCycle_p₃ h k i j)
      (relativeRepresentableTripleCycle_p₁ h j k i)
      (relativeRepresentableTripleCycle_p₂ h i j k)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.RepresentableTripleCycle
