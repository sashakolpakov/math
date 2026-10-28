import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarVerticalAxis
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarFrameTarget
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.KernelScalarRatio

/-! # Zero Scalar Frame -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ZeroScalarFrame.Construction

noncomputable section

/-! The zero-coordinate scalar frame is exactly the original vertical
Poincare unit frame. This simplifies the numerator of the canonical
pairing's frame ratio on arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

omit [IsAlgClosed k] in
theorem poincareUnitFrames_agree_of_both_zero {T : Over (Spec (.of k))}
    (c : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (hf : c ≫ fst D.abelian.scheme A.scheme = 1) (hs : c ≫ snd D.abelian.scheme A.scheme = 1) :
    AxisFrames.Construction.poincareHorizontalUnitFrame D c hf = VerticalUnits.Construction.poincareVerticalUnitFrame D c hs := by
  have hc : c = 1 := by
    apply CartesianMonoidalCategory.hom_ext
    · exact hf.trans (MonObj.one_comp (fst D.abelian.scheme A.scheme)).symm
    · exact hs.trans (MonObj.one_comp (snd D.abelian.scheme A.scheme)).symm
  subst c
  exact VerticalUnits.Construction.poincareUnitFrames_agree_at_zero D T

theorem poincareTorsionScalarFrame_zero (n : ℕ) {T : Over (Spec (.of k))}
    (t : T ⟶ D.abelian.scheme) (ht : t ^ n = 1) :
    TorsionPullbackFrame.Construction.poincareTorsionScalarFrame D n t (1 : T ⟶ A.scheme) ht =
      VerticalUnits.Construction.poincareVerticalUnitFrame D (lift t ((1 : T ⟶ A.scheme) ^ n))
        ((lift_snd _ _).trans (one_pow n)) := by
  unfold TorsionPullbackFrame.Construction.poincareTorsionScalarFrame
  rw [poincareUnitFrames_agree_of_both_zero D (lift (t ^ n) (1 : T ⟶ A.scheme))
    ((lift_fst _ _).trans ht) (lift_snd _ _)]
  exact ScalarVerticalAxis.Construction.poincareScalarVerticalAxis D n t

theorem poincareTorsionScalarFrameTo_zero (n : ℕ) {T : Over (Spec (.of k))}
    (t : T ⟶ D.abelian.scheme) (ht : t ^ n = 1)
    (q : T ⟶ D.abelian.scheme ⊗ A.scheme) (h : lift t ((1 : T ⟶ A.scheme) ^ n) = q)
    (hq : q ≫ snd D.abelian.scheme A.scheme = 1) :
    ScalarFrameTarget.Construction.poincareTorsionScalarFrameTo D n t 1 ht q h = VerticalUnits.Construction.poincareVerticalUnitFrame D q hq := by
  cases h
  exact (ScalarFrameTarget.Construction.poincareTorsionScalarFrameTo_refl D n t 1 ht).trans (poincareTorsionScalarFrame_zero D n t ht)

theorem poincareParameterOriginScalarFrame_vertical {Q : Over (Spec (.of k))}
    (t : Q ⟶ D.abelian.scheme) (n : ℕ) (ht : t ^ n = 1) (U : Over Q.left) :
    KernelScalarRatio.Construction.poincareParameterOriginScalarFrame D t n ht U =
      VerticalUnits.Construction.poincareVerticalUnitFrame D (lift (KernelOriginCoordinates.Construction.poincareParameterDualCoordinate D t U) 1) (lift_snd _ _) :=
  poincareTorsionScalarFrameTo_zero D n (KernelOriginCoordinates.Construction.poincareParameterDualCoordinate D t U)
    (KernelOriginCoordinates.Construction.poincareParameterDualCoordinate_pow D t n ht U) _ _ (lift_snd _ _)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ZeroScalarFrame.Construction
