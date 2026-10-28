import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Sites.Subsheaf

/-! # Over Subfunctor -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.OverSubfunctor

noncomputable section

/-! A subfunctor of points in an over-category also defines a subfunctor
of the underlying object's points. Sheaf descent is preserved. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory Opposite

namespace Construction

universe u v
variable {C : Type u} [Category.{v} C] {S : C} {A : Over S}
  (P : Subfunctor (yoneda.obj A))

def overSubfunctor : Subfunctor (yoneda.obj A.left) where
  obj T := { a | (Over.homMk a rfl : Over.mk (a ≫ A.hom) ⟶ A) ∈ P.obj (op (Over.mk (a ≫ A.hom))) }
  map j a ha := by
    let f : Over.mk ((j.unop ≫ a) ≫ A.hom) ⟶ Over.mk (a ≫ A.hom) :=
      Over.homMk j.unop (Category.assoc _ _ _).symm
    exact P.map f.op ha

theorem overSubfunctor_mem {T : Over S} (a : T ⟶ A) :
    a.left ∈ (overSubfunctor P).obj (op T.left) ↔ a ∈ P.obj (op T) := by
  let e : Over.mk (a.left ≫ A.hom) ≅ T :=
    Over.isoMk (Iso.refl T.left) ((Category.id_comp T.hom).trans a.w.symm)
  let b : Over.mk (a.left ≫ A.hom) ⟶ A := Over.homMk a.left rfl
  have hb : e.inv ≫ b = a := Over.OverMorphism.ext (Category.id_comp a.left)
  have ha : e.hom ≫ a = b := Over.OverMorphism.ext (Category.id_comp a.left)
  constructor
  · intro h
    exact hb ▸ P.map e.inv.op h
  · intro h
    change b ∈ P.obj (op (Over.mk (a.left ≫ A.hom)))
    exact ha ▸ P.map e.hom.op h

theorem overSubfunctor_isSheaf (J : GrothendieckTopology C) [J.Subcanonical]
    (hP : Presieve.IsSheaf (J.over S) P.toFunctor) :
    Presieve.IsSheaf J (overSubfunctor P).toFunctor := by
  have hA := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J) (yoneda.obj A.left)
  have hA' := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J.over S) (yoneda.obj A)
  apply ((overSubfunctor P).isSheaf_iff hA).mpr
  intro T a hR
  let U := Over.mk (a ≫ A.hom)
  let R := (Sieve.overEquiv U).symm ((overSubfunctor P).sieveOfSection a)
  have hc : R ∈ (J.over S) U := by
    rw [GrothendieckTopology.mem_over_iff]
    change Sieve.overEquiv U ((Sieve.overEquiv U).symm ((overSubfunctor P).sieveOfSection a)) ∈ J T.unop
    rw [OrderIso.apply_symm_apply]
    exact hR
  apply (P.isSheaf_iff hA').mp hP (op U) (Over.homMk a rfl)
  apply (J.over S).superset_covering _ hc
  intro V j hj
  change (j.left ≫ a) ∈ (overSubfunctor P).obj (op V.left) at hj
  exact (overSubfunctor_mem P (j ≫ Over.homMk a rfl)).mp hj

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.OverSubfunctor
