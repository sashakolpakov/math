import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardCubicalDefect

/-! # Cubical Defect Bundle -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CubicalDefectBundle.Construction

noncomputable section

/-! An actual line bundle representing the cubical defect, with verified trivial unit faces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k]
variable {A T : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]

def cubicalDefectBundle (l : PicardEq.Construction.Picard A.left) (a b c : T ⟶ A) : PicardEq.Construction.BundledLineBundle T.left :=
  Quotient.out (PicardCubicalDefect.Construction.picardCubicalDefect l a b c)

omit [IsCommMonObj A] in
theorem cubicalDefectBundle_class (l : PicardEq.Construction.Picard A.left) (a b c : T ⟶ A) :
    PicardEq.Construction.lineBundleClass (cubicalDefectBundle l a b c).sheaf (cubicalDefectBundle l a b c).isLineBundle =
      PicardCubicalDefect.Construction.picardCubicalDefect l a b c := Quotient.out_eq _

theorem cubicalDefectBundle_face_trivial {U : Over (Spec (.of k))}
    (f : U ⟶ T) (l : PicardEq.Construction.Picard A.left) (a b c : T ⟶ A)
    (hf : f ≫ a = 1 ∨ f ≫ b = 1 ∨ f ≫ c = 1) :
    Nonempty ((Scheme.Modules.pullback f.left).obj (cubicalDefectBundle l a b c).sheaf ≅
      LineBundle.Construction.structureSheafModule U.left) := by
  let L := cubicalDefectBundle l a b c
  apply (PicardEq.Construction.lineBundleClass_eq_iff (LineBundle.Construction.isLineBundle_pullback f.left L.sheaf L.isLineBundle)
    (LineBundle.Construction.isLineBundle_structureSheaf U.left)).mp
  change PicardPullback.Construction.picardPullback f.left (PicardEq.Construction.lineBundleClass L.sheaf L.isLineBundle) = 0
  rw [cubicalDefectBundle_class]
  exact PicardCubicalDefect.Construction.picardCubicalDefect_pullback_zero_of_face f l a b c hf

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CubicalDefectBundle.Construction
