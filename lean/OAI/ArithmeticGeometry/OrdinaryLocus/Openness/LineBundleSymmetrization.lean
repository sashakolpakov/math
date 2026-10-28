import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardMultiplication

/-! # Line Bundle Symmetrization -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleSymmetrization.Construction

noncomputable section

/-! Symmetrization of line bundles on commutative group schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem groupInversion_comp_self {S : Scheme} (A : Over S) [GrpObj A] :
    ((𝟙 A : A ⟶ A)⁻¹).left ≫ ((𝟙 A : A ⟶ A)⁻¹).left = 𝟙 A.left := by
  have h : (𝟙 A : A ⟶ A)⁻¹ ≫ (𝟙 A : A ⟶ A)⁻¹ = 𝟙 A := by
    rw [GrpObj.comp_inv, Category.comp_id, inv_inv]
  exact congrArg Over.Hom.left h

theorem picardInversion_involutive {S : Scheme} (A : Over S) [GrpObj A] :
    Function.Involutive (PicardPullback.Construction.picardPullback ((𝟙 A : A ⟶ A)⁻¹).left) := by
  intro l
  have h := congrArg (fun f : PicardEq.Construction.Picard A.left →+ PicardEq.Construction.Picard A.left ↦ f l)
    (PicardPullback.Construction.picardPullback_comp ((𝟙 A : A ⟶ A)⁻¹).left ((𝟙 A : A ⟶ A)⁻¹).left)
  rw [groupInversion_comp_self, PicardPullback.Construction.picardPullback_id] at h
  exact h.symm

theorem picardSymmetrization_invariant {S : Scheme} (A : Over S) [GrpObj A] (l : PicardEq.Construction.Picard A.left) :
    PicardPullback.Construction.picardPullback ((𝟙 A : A ⟶ A)⁻¹).left
        (l + PicardPullback.Construction.picardPullback ((𝟙 A : A ⟶ A)⁻¹).left l) =
      l + PicardPullback.Construction.picardPullback ((𝟙 A : A ⟶ A)⁻¹).left l := by
  rw [map_add, picardInversion_involutive]
  exact add_comm _ _

def symmetrizedLineBundle {S : Scheme} (A : Over S) [GrpObj A] (M : A.left.Modules) : A.left.Modules :=
  SheafTensor.Construction.sheafTensor M ((Scheme.Modules.pullback ((𝟙 A : A ⟶ A)⁻¹).left).obj M)

theorem isLineBundle_symmetrized {S : Scheme} (A : Over S) [GrpObj A]
    {M : A.left.Modules} (hM : LineBundle.Construction.IsLineBundle M) : LineBundle.Construction.IsLineBundle (symmetrizedLineBundle A M) :=
  TensorRestriction.Construction.isLineBundle_sheafTensor hM (LineBundle.Construction.isLineBundle_pullback ((𝟙 A : A ⟶ A)⁻¹).left M hM)

theorem symmetrizedLineBundle_invariant {S : Scheme} (A : Over S) [GrpObj A]
    {M : A.left.Modules} (hM : LineBundle.Construction.IsLineBundle M) :
    Nonempty ((Scheme.Modules.pullback ((𝟙 A : A ⟶ A)⁻¹).left).obj (symmetrizedLineBundle A M) ≅
      symmetrizedLineBundle A M) := by
  apply (PicardEq.Construction.lineBundleClass_eq_iff
    (LineBundle.Construction.isLineBundle_pullback ((𝟙 A : A ⟶ A)⁻¹).left _ (isLineBundle_symmetrized A hM))
    (isLineBundle_symmetrized A hM)).mp
  exact picardSymmetrization_invariant A (PicardEq.Construction.lineBundleClass M hM)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleSymmetrization.Construction
