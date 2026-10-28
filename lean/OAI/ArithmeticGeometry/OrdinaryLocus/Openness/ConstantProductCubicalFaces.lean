import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductPointFiber
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CubicalDefectBundle

/-! # Constant Product Cubical Faces -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductCubicalFaces.Construction

noncomputable section

/-! The cubical defect pulled to two pointed factors has trivial axes and unit fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K] (A B G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G]
variable (a : A ⟶ G) (b : B ⟶ G) (l : PicardEq.Construction.Picard G.left)

def constantProductCubicalBundle : PicardEq.Construction.BundledLineBundle (ConstantProductCoordinates.Construction.constantProduct A B G).left :=
  CubicalDefectBundle.Construction.cubicalDefectBundle l (ConstantProductCoordinates.Construction.constantProductLeft A B G ≫ fst A G ≫ a)
    (ConstantProductCoordinates.Construction.constantProductRight A B G ≫ fst B G ≫ b) (ConstantProductCoordinates.Construction.constantProductBase A B G)

theorem constantProductCubicalBundle_left_trivial
    (sB : 𝟙_ (Over (Spec (.of K))) ⟶ B) (hb : sB ≫ b = η[G]) :
    Nonempty ((Scheme.Modules.pullback (ConstantProductCoordinates.Construction.constantProductLeftAxis A B G sB).left).obj
      (constantProductCubicalBundle A B G a b l).sheaf ≅ LineBundle.Construction.structureSheafModule (A ⊗ G).left) := by
  have hc : ConstantProductCoordinates.Construction.constantFamilySection B G sB ≫ fst B G ≫ b = (1 : G ⟶ G) := by
    rw [← Category.assoc, ConstantProductCoordinates.Construction.constantFamilySection_factor, Category.assoc, hb]
    rfl
  apply CubicalDefectBundle.Construction.cubicalDefectBundle_face_trivial (ConstantProductCoordinates.Construction.constantProductLeftAxis A B G sB) l
  apply Or.inr ∘ Or.inl
  rw [← Category.assoc, ConstantProductCoordinates.Construction.constantProductLeftAxis_right, Category.assoc, hc, MonObj.comp_one]

theorem constantProductCubicalBundle_right_trivial
    (sA : 𝟙_ (Over (Spec (.of K))) ⟶ A) (ha : sA ≫ a = η[G]) :
    Nonempty ((Scheme.Modules.pullback (ConstantProductCoordinates.Construction.constantProductRightAxis A B G sA).left).obj
      (constantProductCubicalBundle A B G a b l).sheaf ≅ LineBundle.Construction.structureSheafModule (B ⊗ G).left) := by
  have hc : ConstantProductCoordinates.Construction.constantFamilySection A G sA ≫ fst A G ≫ a = (1 : G ⟶ G) := by
    rw [← Category.assoc, ConstantProductCoordinates.Construction.constantFamilySection_factor, Category.assoc, ha]
    rfl
  apply CubicalDefectBundle.Construction.cubicalDefectBundle_face_trivial (ConstantProductCoordinates.Construction.constantProductRightAxis A B G sA) l
  apply Or.inl
  rw [← Category.assoc, ConstantProductCoordinates.Construction.constantProductRightAxis_left, Category.assoc, hc, MonObj.comp_one]

theorem constantProductCubicalBundle_unit_trivial :
    Nonempty ((Scheme.Modules.pullback (ConstantProductPointFiber.Construction.constantProductPointFiber A B G η[G]).left).obj
      (constantProductCubicalBundle A B G a b l).sheaf ≅ LineBundle.Construction.structureSheafModule (A ⊗ B).left) := by
  apply CubicalDefectBundle.Construction.cubicalDefectBundle_face_trivial (ConstantProductPointFiber.Construction.constantProductPointFiber A B G η[G]) l
  apply Or.inr ∘ Or.inr
  exact ConstantProductPointFiber.Construction.constantProductPointFiber_base A B G η[G]

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductCubicalFaces.Construction
