import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.MultiplicationIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AtIdentity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassGroup

/-! # Class Powers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Tensor powers of actual Poincare classes classify powers of the
corresponding dual-valued points. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A) (T : Over (Spec (.of K)))

def Dual.Data.DualAbelianData.poincareAtClassHom : (T ⟶ D.abelian.scheme) →*
    Line.Bundles.LineBundle.IsoClass ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T) where
  toFun f := Line.Bundles.LineBundle.classOf (D.poincareAt f)
  map_one' := Quotient.sound ⟨D.poincareAt_oneIso T⟩
  map_mul' f h := Quotient.sound (D.poincareAt_mul_iso_overField f h)

theorem Dual.Data.DualAbelianData.poincareAt_class_pow (f : T ⟶ D.abelian.scheme) (n : ℕ) :
    Line.Bundles.LineBundle.classOf (D.poincareAt (f ^ n)) = Line.Bundles.LineBundle.classOf (D.poincareAt f) ^ n :=
  (D.poincareAtClassHom T).map_pow f n

theorem Dual.Data.DualAbelianData.poincareAt_pow_eq_of_classPower_eq (f h : T ⟶ D.abelian.scheme) (n : ℕ)
    (he : Line.Bundles.LineBundle.classOf (D.poincareAt f) ^ n = Line.Bundles.LineBundle.classOf (D.poincareAt h) ^ n) :
    f ^ n = h ^ n := by
  apply D.poincareAt_class_injective T
  exact (D.poincareAt_class_pow T f n).trans
    (he.trans (D.poincareAt_class_pow T h n).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
