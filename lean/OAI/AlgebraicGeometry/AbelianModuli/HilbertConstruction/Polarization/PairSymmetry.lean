import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PairClass
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PairNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassGroup

/-! # Pair Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.PairSymmetry

noncomputable section

/-! A normalized polarization formula makes its Poincare pairing symmetric
on every actual test scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {k : Type u} [Field k] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of k))}
variable (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme)

def poincareAt_pairPullbackIso {T : Over (Spec (.of k))} (x y : T ⟶ A.scheme) :
    ((D.poincareAt p).pullback (lift x y).left).sheaf ≅ (D.poincarePair (x ≫ p) y).sheaf := by
  have h : lift x y ≫ (p ▷ A.scheme) = lift (x ≫ p) y := by
    simp only [lift_whiskerRight]
  exact (Scheme.Modules.pullbackComp (lift x y).left ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map p)).app
      D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).app D.poincare.sheaf ≪≫
    (D.poincarePairDirectIso (x ≫ p) y).symm

variable (L : Line.Bundles.LineBundle A.scheme.left)
variable (e : (((D.poincareAt p).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
  (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)

def polarizationPairFormulaIso {T : Over (Spec (.of k))} (x y : T ⟶ A.scheme) :
    (((D.poincarePair (x ≫ p) y).tensor (L.pullback x.left)).tensor (L.pullback y.left)).sheaf ≅
      (L.pullback (x * y).left).sheaf := by
  let z := (lift x y).left
  let B := D.poincareAt p
  let L₁ := L.pullback (fst A.scheme A.scheme).left
  let L₂ := L.pullback (snd A.scheme A.scheme).left
  let ex : (L₁.pullback z).sheaf ≅ (L.pullback x.left).sheaf :=
    (Scheme.Modules.pullbackComp z (fst A.scheme A.scheme).left).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (lift_fst x y))).app L.sheaf
  let ey : (L₂.pullback z).sheaf ≅ (L.pullback y.left).sheaf :=
    (Scheme.Modules.pullbackComp z (snd A.scheme A.scheme).left).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (lift_snd x y))).app L.sheaf
  let ez : ((L.pullback μ[A.scheme].left).pullback z).sheaf ≅ (L.pullback (x * y).left).sheaf :=
    (Scheme.Modules.pullbackComp z μ[A.scheme].left).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (Hom.mul_def x y)).symm).app L.sheaf
  let lhs : (((B.tensor L₁).tensor L₂).pullback z).sheaf ≅
      (((D.poincarePair (x ≫ p) y).tensor (L.pullback x.left)).tensor (L.pullback y.left)).sheaf :=
    Line.Bundles.LineBundle.tensorBaseChangeIso z (B.tensor L₁) L₂ ≪≫
      Tensor.Bifunctor.tensorModuleMapIso (Line.Bundles.LineBundle.tensorBaseChangeIso z B L₁) (Iso.refl _) ≪≫
      Tensor.Bifunctor.tensorModuleMapIso (Tensor.Bifunctor.tensorModuleMapIso (poincareAt_pairPullbackIso D p x y) ex) ey
  exact lhs.symm ≪≫ (Scheme.Modules.pullback z).mapIso e ≪≫ ez

include L e in
theorem polarizationPairClass_symmetric {T : Over (Spec (.of k))} (x y : T ⟶ A.scheme) :
    D.poincarePairClass T (x ≫ p) y = D.poincarePairClass T (y ≫ p) x := by
  have hx : (D.poincarePairClass T (x ≫ p) y * Line.Bundles.LineBundle.classOf (L.pullback x.left)) *
      Line.Bundles.LineBundle.classOf (L.pullback y.left) = Line.Bundles.LineBundle.classOf (L.pullback (x * y).left) :=
    Quotient.sound ⟨polarizationPairFormulaIso D p L e x y⟩
  have hy : (D.poincarePairClass T (y ≫ p) x * Line.Bundles.LineBundle.classOf (L.pullback y.left)) *
      Line.Bundles.LineBundle.classOf (L.pullback x.left) = Line.Bundles.LineBundle.classOf (L.pullback (y * x).left) :=
    Quotient.sound ⟨polarizationPairFormulaIso D p L e y x⟩
  have hxy : D.poincarePairClass T (x ≫ p) y *
      (Line.Bundles.LineBundle.classOf (L.pullback x.left) * Line.Bundles.LineBundle.classOf (L.pullback y.left)) =
    D.poincarePairClass T (y ≫ p) x *
      (Line.Bundles.LineBundle.classOf (L.pullback x.left) * Line.Bundles.LineBundle.classOf (L.pullback y.left)) := by
    calc
      _ = Line.Bundles.LineBundle.classOf (L.pullback (x * y).left) := by simpa only [mul_assoc] using hx
      _ = Line.Bundles.LineBundle.classOf (L.pullback (y * x).left) := congrArg
        (fun a : T ⟶ A.scheme => Line.Bundles.LineBundle.classOf (L.pullback a.left)) (mul_comm x y)
      _ = _ := hy.symm.trans (by
        rw [mul_assoc, mul_comm (Line.Bundles.LineBundle.classOf (L.pullback y.left))
          (Line.Bundles.LineBundle.classOf (L.pullback x.left))])
  exact mul_right_cancel hxy

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.PairSymmetry
