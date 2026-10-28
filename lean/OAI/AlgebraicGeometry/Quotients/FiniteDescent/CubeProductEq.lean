import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductBase

/-! # Cube Product Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductEq

noncomputable section

/-! Any three morphisms to the group give a map to the product used for
the universal cube class. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.CubeProductLift

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates

variable {K : Type u} [Field K] (A : Over (Spec (.of K))) {T : Over (Spec (.of K))}
variable (a b c : T ⟶ A)

def pair (a c : T ⟶ A) : T.left ⟶ pullback A.hom A.hom :=
  pullback.lift a.left c.left (a.w.trans c.w.symm)

def map : T.left ⟶ CubeProductBase.Construction.CubeProductCoordinates.total A A.hom A.hom :=
  pullback.lift (pair A a c) (pair A b c) (by
    simp only [pair, CubeProductBase.Construction.CubeProductCoordinates.leftBase, CubeProductBase.Construction.CubeProductCoordinates.rightBase, pullback.lift_snd])

theorem first_projection : map A a b c ≫
    pullback.fst (CubeProductBase.Construction.CubeProductCoordinates.leftBase A A.hom) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A A.hom) ≫ pullback.fst A.hom A.hom = a.left := by
  simp only [map, pair, pullback.lift_fst_assoc, pullback.lift_fst]

theorem second_projection : map A a b c ≫
    pullback.snd (CubeProductBase.Construction.CubeProductCoordinates.leftBase A A.hom) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A A.hom) ≫ pullback.fst A.hom A.hom = b.left := by
  simp only [map, pair, pullback.lift_snd_assoc, pullback.lift_fst]

theorem third_projection : map A a b c ≫ CubeProductBase.Construction.CubeProductCoordinates.projection A A.hom A.hom = c.left := by
  simp only [map, CubeProductBase.Construction.CubeProductCoordinates.projection, pair, pullback.lift_fst_assoc, CubeProductBase.Construction.CubeProductCoordinates.leftBase, pullback.lift_snd]

def hom : T ⟶ CubeProductBase.Construction.CubeProductCoordinates.ambient A A.hom A.hom := Over.homMk (map A a b c) (by
  change map A a b c ≫ (CubeProductBase.Construction.CubeProductCoordinates.projection A A.hom A.hom ≫ A.hom) = T.hom
  rw [← Category.assoc, third_projection]
  exact c.w)

theorem first_eq : CubeProductLift.hom A a b c ≫ CubeProductBase.Construction.CubeProductCoordinates.first A A.hom A.hom (𝟙 A.left) (Category.id_comp _) = a := by
  apply Over.OverMorphism.ext
  change map A a b c ≫ (_ ≫ _ ≫ 𝟙 A.left) = a.left
  rw [Category.comp_id, first_projection]

theorem second_eq : CubeProductLift.hom A a b c ≫ CubeProductBase.Construction.CubeProductCoordinates.second A A.hom A.hom (𝟙 A.left) (Category.id_comp _) = b := by
  apply Over.OverMorphism.ext
  change map A a b c ≫ (_ ≫ _ ≫ 𝟙 A.left) = b.left
  rw [Category.comp_id, second_projection]

theorem third_eq : CubeProductLift.hom A a b c ≫ CubeProductBase.Construction.CubeProductCoordinates.third A A.hom A.hom = c :=
  Over.OverMorphism.ext (third_projection A a b c)

end Construction.CubeProductLift

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductEq
