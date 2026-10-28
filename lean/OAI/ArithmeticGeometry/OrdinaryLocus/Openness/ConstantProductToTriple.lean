import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductAssociativity
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductCubicalFaces
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TripleCube

/-! # Constant Product To Triple -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductToTriple.Construction

noncomputable section

/-! The cubical defect on pointed factors is the pullback of the group triple-product defect. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K] (A B G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G]
variable (a : A ⟶ G) (b : B ⟶ G)

def constantProductToTriple : ConstantProductCoordinates.Construction.constantProduct A B G ⟶ TripleCube.Construction.cubeDomain G :=
  (ConstantProductAssociativity.Construction.constantProductAssocIso A B G).hom ≫ ((a ⊗ₘ b) ⊗ₘ 𝟙 G)

omit [GrpObj G] [IsCommMonObj G] in
theorem constantProductToTriple_first :
    constantProductToTriple A B G a b ≫ TripleCube.Construction.cubeFirst G = ConstantProductCoordinates.Construction.constantProductLeft A B G ≫ fst A G ≫ a := by
  simp only [constantProductToTriple, TripleCube.Construction.cubeFirst, Category.assoc, tensorHom_fst_assoc,
    tensorHom_fst]
  exact congrArg (fun f => f ≫ a) (ConstantProductAssociativity.Construction.constantProductAssocIso_first A B G)

omit [GrpObj G] [IsCommMonObj G] in
theorem constantProductToTriple_second :
    constantProductToTriple A B G a b ≫ TripleCube.Construction.cubeSecond G = ConstantProductCoordinates.Construction.constantProductRight A B G ≫ fst B G ≫ b := by
  simp only [constantProductToTriple, TripleCube.Construction.cubeSecond, Category.assoc, tensorHom_fst_assoc, tensorHom_snd]
  exact congrArg (fun f => f ≫ b) (ConstantProductAssociativity.Construction.constantProductAssocIso_second A B G)

omit [GrpObj G] [IsCommMonObj G] in
theorem constantProductToTriple_third :
    constantProductToTriple A B G a b ≫ TripleCube.Construction.cubeThird G = ConstantProductCoordinates.Construction.constantProductBase A B G := by
  rw [constantProductToTriple, TripleCube.Construction.cubeThird, Category.assoc, tensorHom_snd, Category.comp_id,
    ConstantProductAssociativity.Construction.constantProductAssocIso_base]

omit [IsCommMonObj G] in
theorem constantProductToTriple_cube_class (l : PicardEq.Construction.Picard G.left) :
    PicardPullback.Construction.picardPullback (constantProductToTriple A B G a b).left
      (PicardEq.Construction.lineBundleClass (TripleCube.Construction.tripleCubeBundle G l).sheaf (TripleCube.Construction.tripleCubeBundle G l).isLineBundle) =
    PicardEq.Construction.lineBundleClass (ConstantProductCubicalFaces.Construction.constantProductCubicalBundle A B G a b l).sheaf
      (ConstantProductCubicalFaces.Construction.constantProductCubicalBundle A B G a b l).isLineBundle := by
  dsimp only [TripleCube.Construction.tripleCubeBundle, ConstantProductCubicalFaces.Construction.constantProductCubicalBundle]
  rw [CubicalDefectBundle.Construction.cubicalDefectBundle_class, PicardCubicalDefect.Construction.picardCubicalDefect_pullback,
    constantProductToTriple_first, constantProductToTriple_second, constantProductToTriple_third]
  exact (CubicalDefectBundle.Construction.cubicalDefectBundle_class l _ _ _).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductToTriple.Construction
