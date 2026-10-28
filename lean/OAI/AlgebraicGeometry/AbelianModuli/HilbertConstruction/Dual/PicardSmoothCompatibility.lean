import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.PoincareClasses
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.MonoidUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.Support

/-! # Picard Smooth Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual

noncomputable section

/-! Smooth connected rigidity identifies the dual's tensor multiplication with its given group law over any field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}

theorem Data.DualAbelianData.tensorMultiplication_eq_groupMul_overField (D : Data.DualAbelianData A)
    : D.tensorMultiplication = μ[D.abelian.scheme] := by
  have : ConnectedSpace D.abelian.scheme.left := D.abelian.connected_overField
  have : IsReduced (D.abelian.scheme ⊗ D.abelian.scheme).left :=
    D.abelian.selfProduct_reduced_overField
  exact Smooth.MonoidUniqueness.smoothMonoid_multiplication_unique D.abelian.scheme D.picardMonoid D.picardMonoid_one

theorem Data.DualAbelianData.tensorProductPoint_eq_mul_overField (D : Data.DualAbelianData A)
    {T : Over (Spec (.of K))}
    (x y : T ⟶ D.abelian.scheme) : D.tensorProductPoint x y = x * y :=
  congrArg (fun a => lift x y ≫ a) D.tensorMultiplication_eq_groupMul_overField

theorem Data.DualAbelianData.homEquiv_mul_overField (D : Data.DualAbelianData A)
    {T : Over (Spec (.of K))} (x y : T ⟶ D.abelian.scheme) :
    D.representable.homEquiv (x * y) = D.representable.homEquiv x * D.representable.homEquiv y :=
  (congrArg D.representable.homEquiv (D.tensorProductPoint_eq_mul_overField x y)).symm.trans
    (D.tensorProductPoint_classifies x y)

def Data.DualAbelianData.homEquivMonoidHom_overField (D : Data.DualAbelianData A)
    (T : Over (Spec (.of K))) : D.abelian.Points T →* A.HomogeneousPicardSections T where
  toFun := D.representable.homEquiv
  map_one' := (D.origin T).trans (A.trivialHomogeneousPicardClass_eq_one T)
  map_mul' := D.homEquiv_mul_overField

theorem Data.DualAbelianData.homogeneousPicardSection_isUnit_overField (D : Data.DualAbelianData A)
    (T : Over (Spec (.of K)))
    (q : A.HomogeneousPicardSections T) : IsUnit q := by
  obtain ⟨x, rfl⟩ := D.representable.homEquiv.surjective q
  have hx : IsUnit (x : D.abelian.Points T) := ⟨⟨x, x⁻¹, mul_inv_cancel x, inv_mul_cancel x⟩, rfl⟩
  exact hx.map (D.homEquivMonoidHom_overField T)

theorem Data.DualAbelianData.poincareAt_mul_class_overField (D : Data.DualAbelianData A)
    {T : Over (Spec (.of K))} (x y : T ⟶ D.abelian.scheme) :
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (Line.Bundles.LineBundle.classOf (D.poincareAt (x * y))) =
      (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)
        (Line.Bundles.LineBundle.classOf ((D.poincareAt x).tensor (D.poincareAt y))) := by
  rw [← D.tensorProductPoint_eq_mul_overField]
  exact D.poincareAt_tensorProductPoint_class x y

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual
