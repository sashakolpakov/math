import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.PicardMultiplication

/-! # Picard Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual

noncomputable section

/-! The multiplication represented by tensor product, on arbitrary test-scheme points of the dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {g : ℕ} {S : Scheme.{u}} {A : Abelian.Schemes.AbelianScheme g S}

def Data.DualAbelianData.tensorProductPoint (D : Data.DualAbelianData A) {T : Over S}
    (x y : T ⟶ D.abelian.scheme) : T ⟶ D.abelian.scheme :=
  lift x y ≫ D.tensorMultiplication

theorem Data.DualAbelianData.tensorProductPoint_classifies (D : Data.DualAbelianData A) {T : Over S}
    (x y : T ⟶ D.abelian.scheme) :
    D.representable.homEquiv (D.tensorProductPoint x y) =
      D.representable.homEquiv x * D.representable.homEquiv y := by
  have hx : A.homogeneousPicardSheaf.obj.map (lift x y).op
      (D.representable.homEquiv (fst D.abelian.scheme D.abelian.scheme)) = D.representable.homEquiv x :=
    (D.representable.homEquiv_comp (lift x y) (fst D.abelian.scheme D.abelian.scheme)).symm.trans
      (congrArg D.representable.homEquiv (lift_fst x y))
  have hy : A.homogeneousPicardSheaf.obj.map (lift x y).op
      (D.representable.homEquiv (snd D.abelian.scheme D.abelian.scheme)) = D.representable.homEquiv y :=
    (D.representable.homEquiv_comp (lift x y) (snd D.abelian.scheme D.abelian.scheme)).symm.trans
      (congrArg D.representable.homEquiv (lift_snd x y))
  exact (D.representable.homEquiv_comp (lift x y) D.tensorMultiplication).trans
    ((congrArg (fun z => A.homogeneousPicardSheaf.obj.map (lift x y).op z)
      D.tensorMultiplication_classifies).trans
        ((PresheafMonoidSections.presheafSections_map_mul A.homogeneousPicardSheaf.obj (lift x y).op _ _).trans
          (congrArg₂ (fun a b : A.HomogeneousPicardSections T => a * b) hx hy)))

theorem Data.DualAbelianData.tensorProductPoint_comm (D : Data.DualAbelianData A) {T : Over S}
    (x y : T ⟶ D.abelian.scheme) : D.tensorProductPoint x y = D.tensorProductPoint y x := by
  apply D.representable.homEquiv.injective
  rw [Data.DualAbelianData.tensorProductPoint_classifies, Data.DualAbelianData.tensorProductPoint_classifies, mul_comm]

theorem Data.DualAbelianData.tensorProductPoint_assoc (D : Data.DualAbelianData A) {T : Over S}
    (x y z : T ⟶ D.abelian.scheme) :
    D.tensorProductPoint (D.tensorProductPoint x y) z = D.tensorProductPoint x (D.tensorProductPoint y z) := by
  apply D.representable.homEquiv.injective
  simp only [Data.DualAbelianData.tensorProductPoint_classifies, mul_assoc]

theorem Data.DualAbelianData.tensorProductPoint_one (D : Data.DualAbelianData A) {T : Over S}
    (x : T ⟶ D.abelian.scheme) : D.tensorProductPoint x 1 = x := by
  apply D.representable.homEquiv.injective
  rw [Data.DualAbelianData.tensorProductPoint_classifies, D.origin, A.trivialHomogeneousPicardClass_eq_one, mul_one]

theorem Data.DualAbelianData.tensorProductPoint_one_left (D : Data.DualAbelianData A) {T : Over S}
    (x : T ⟶ D.abelian.scheme) : D.tensorProductPoint 1 x = x :=
  (D.tensorProductPoint_comm 1 x).trans (D.tensorProductPoint_one x)

theorem Data.DualAbelianData.tensorProductPoint_natural (D : Data.DualAbelianData A) {T U : Over S}
    (f : U ⟶ T) (x y : T ⟶ D.abelian.scheme) :
    f ≫ D.tensorProductPoint x y = D.tensorProductPoint (f ≫ x) (f ≫ y) := by
  change f ≫ lift x y ≫ D.tensorMultiplication = lift (f ≫ x) (f ≫ y) ≫ D.tensorMultiplication
  rw [← Category.assoc, comp_lift]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual
