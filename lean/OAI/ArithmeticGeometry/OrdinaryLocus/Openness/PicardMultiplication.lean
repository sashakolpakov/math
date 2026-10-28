import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CubicalAlgebra
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication

/-! # Picard Multiplication -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardMultiplication.Construction

noncomputable section

/-! Multiplication pullbacks from the cubical identity in the Picard group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

def endomorphismPicardClass {k : Type} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] (l : PicardEq.Construction.Picard A.left) :
    Additive (A ⟶ A) → PicardEq.Construction.Picard A.left :=
  fun f ↦ PicardPullback.Construction.picardPullback f.toMul.left l

theorem endomorphismPicardClass_zero {k : Type} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] (l : PicardEq.Construction.Picard A.left) :
    endomorphismPicardClass A l 0 = 0 := by
  change PicardPullback.Construction.picardPullback (A.hom ≫ (η[A]).left) l = 0
  exact PicardField.Construction.picardPullback_constant A.hom (η[A]).left l

theorem picardMultiplication_of_cubical {k : Type} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] (l : PicardEq.Construction.Picard A.left)
    (hc : CubicalAlgebra.Construction.IsCubical (endomorphismPicardClass A l))
    (hs : PicardPullback.Construction.picardPullback ((𝟙 A : A ⟶ A)⁻¹).left l = l) (n : ℕ) :
    PicardPullback.Construction.picardPullback (Multiplication.Construction.multiplicationMap A n).left l = n ^ 2 • l := by
  let x : Additive (A ⟶ A) := Additive.ofMul (𝟙 A)
  have hid : endomorphismPicardClass A l x = l := by
    change PicardPullback.Construction.picardPullback (𝟙 A.left) l = l
    rw [PicardPullback.Construction.picardPullback_id]
    rfl
  have hx : endomorphismPicardClass A l (-x) = endomorphismPicardClass A l x := hs.trans hid.symm
  have h := CubicalAlgebra.Construction.cubical_nsmul_of_symmetric (endomorphismPicardClass_zero A l) hc x hx n
  rw [hid] at h
  exact h

theorem symmetricLineBundleMultiplication_of_cubical {k : Type} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    (M : A.left.Modules) (hM : LineBundle.Construction.IsLineBundle M)
    (hc : CubicalAlgebra.Construction.IsCubical (endomorphismPicardClass A (PicardEq.Construction.lineBundleClass M hM)))
    (hs : Nonempty ((Scheme.Modules.pullback ((𝟙 A : A ⟶ A)⁻¹).left).obj M ≅ M)) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback (Multiplication.Construction.multiplicationMap A n).left).obj M ≅ TensorRestriction.Construction.sheafTensorPower M (n ^ 2)) := by
  apply (PicardEq.Construction.lineBundleClass_eq_iff
    (LineBundle.Construction.isLineBundle_pullback (Multiplication.Construction.multiplicationMap A n).left M hM)
    (TensorRestriction.Construction.isLineBundle_sheafTensorPower hM (n ^ 2))).mp
  rw [PicardEq.Construction.lineBundleClass_tensorPower hM]
  apply picardMultiplication_of_cubical A _ hc
  exact (PicardEq.Construction.lineBundleClass_eq_iff
    (LineBundle.Construction.isLineBundle_pullback ((𝟙 A : A ⟶ A)⁻¹).left M hM) hM).mpr hs

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardMultiplication.Construction
