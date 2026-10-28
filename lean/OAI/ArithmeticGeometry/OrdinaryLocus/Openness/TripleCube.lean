import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CubicalDefectBundle
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardMultiplication

/-! # Triple Cube -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TripleCube.Construction

noncomputable section

/-! The cubical defect on the actual triple product, and its three unit-face trivializations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]

abbrev cubeDomain : Over (Spec (.of k)) := (A ⊗ A) ⊗ A

def cubeFirst : cubeDomain A ⟶ A := fst (A ⊗ A) A ≫ fst A A
def cubeSecond : cubeDomain A ⟶ A := fst (A ⊗ A) A ≫ snd A A
def cubeThird : cubeDomain A ⟶ A := snd (A ⊗ A) A

def cubeFaceFirst : A ⊗ A ⟶ cubeDomain A := lift (lift 1 (fst A A)) (snd A A)
def cubeFaceSecond : A ⊗ A ⟶ cubeDomain A := lift (lift (fst A A) 1) (snd A A)
def cubeFaceThird : A ⊗ A ⟶ cubeDomain A := lift (𝟙 (A ⊗ A)) 1

def tripleCubeBundle (l : PicardEq.Construction.Picard A.left) : PicardEq.Construction.BundledLineBundle (cubeDomain A).left :=
  CubicalDefectBundle.Construction.cubicalDefectBundle l (cubeFirst A) (cubeSecond A) (cubeThird A)

theorem tripleCubeBundle_first_trivial (l : PicardEq.Construction.Picard A.left) :
    Nonempty ((Scheme.Modules.pullback (cubeFaceFirst A).left).obj (tripleCubeBundle A l).sheaf ≅
      LineBundle.Construction.structureSheafModule (A ⊗ A).left) := by
  apply CubicalDefectBundle.Construction.cubicalDefectBundle_face_trivial (cubeFaceFirst A) l (cubeFirst A) (cubeSecond A) (cubeThird A)
  apply Or.inl
  simp only [cubeFaceFirst, cubeFirst, lift_fst_assoc, lift_fst]

theorem tripleCubeBundle_second_trivial (l : PicardEq.Construction.Picard A.left) :
    Nonempty ((Scheme.Modules.pullback (cubeFaceSecond A).left).obj (tripleCubeBundle A l).sheaf ≅
      LineBundle.Construction.structureSheafModule (A ⊗ A).left) := by
  apply CubicalDefectBundle.Construction.cubicalDefectBundle_face_trivial (cubeFaceSecond A) l (cubeFirst A) (cubeSecond A) (cubeThird A)
  apply Or.inr ∘ Or.inl
  simp only [cubeFaceSecond, cubeSecond, lift_fst_assoc, lift_snd]

theorem tripleCubeBundle_third_trivial (l : PicardEq.Construction.Picard A.left) :
    Nonempty ((Scheme.Modules.pullback (cubeFaceThird A).left).obj (tripleCubeBundle A l).sheaf ≅
      LineBundle.Construction.structureSheafModule (A ⊗ A).left) := by
  apply CubicalDefectBundle.Construction.cubicalDefectBundle_face_trivial (cubeFaceThird A) l (cubeFirst A) (cubeSecond A) (cubeThird A)
  apply Or.inr ∘ Or.inr
  simp only [cubeFaceThird, cubeThird, lift_snd]

omit [IsCommMonObj A] in
theorem picardCubicalDefect_zero_of_tripleCube_trivial
    (l : PicardEq.Construction.Picard A.left)
    (he : Nonempty ((tripleCubeBundle A l).sheaf ≅ LineBundle.Construction.structureSheafModule (cubeDomain A).left))
    {T : Over (Spec (.of k))} (a b c : T ⟶ A) : PicardCubicalDefect.Construction.picardCubicalDefect l a b c = 0 := by
  have hz := (PicardEq.Construction.lineBundleClass_eq_iff (tripleCubeBundle A l).isLineBundle
    (LineBundle.Construction.isLineBundle_structureSheaf (cubeDomain A).left)).mpr he
  have hz' : PicardCubicalDefect.Construction.picardCubicalDefect l (cubeFirst A) (cubeSecond A) (cubeThird A) = 0 :=
    (CubicalDefectBundle.Construction.cubicalDefectBundle_class l (cubeFirst A) (cubeSecond A) (cubeThird A)).symm.trans hz
  let f : T ⟶ cubeDomain A := lift (lift a b) c
  have h := congrArg (PicardPullback.Construction.picardPullback f.left) hz'
  rw [PicardCubicalDefect.Construction.picardCubicalDefect_pullback, map_zero] at h
  simpa only [f, cubeFirst, cubeSecond, cubeThird, lift_fst_assoc, lift_fst, lift_snd] using h

theorem endomorphismPicardClass_isCubical_of_tripleCube_trivial
    {k : Type} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    (l : PicardEq.Construction.Picard A.left)
    (he : Nonempty ((tripleCubeBundle A l).sheaf ≅ LineBundle.Construction.structureSheafModule (cubeDomain A).left)) :
    CubicalAlgebra.Construction.IsCubical (PicardMultiplication.Construction.endomorphismPicardClass A l) := by
  intro a b c
  have h := picardCubicalDefect_zero_of_tripleCube_trivial A l he a.toMul b.toMul c.toMul
  change PicardPullback.Construction.picardPullback (a.toMul * b.toMul * c.toMul).left l + PicardPullback.Construction.picardPullback a.toMul.left l +
    PicardPullback.Construction.picardPullback b.toMul.left l + PicardPullback.Construction.picardPullback c.toMul.left l =
      PicardPullback.Construction.picardPullback (a.toMul * b.toMul).left l + PicardPullback.Construction.picardPullback (a.toMul * c.toMul).left l +
        PicardPullback.Construction.picardPullback (b.toMul * c.toMul).left l
  exact sub_eq_zero.mp (by simpa only [PicardCubicalDefect.Construction.picardCubicalDefect, sub_sub] using h)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TripleCube.Construction
