import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicativeBilinearParallelogram
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.PowerIsomorphism

/-! # Parallelogram -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.Parallelogram

noncomputable section

/-! The Poincare graph line bundle satisfies the parallelogram identity on arbitrary test-scheme points, as an isomorphism of actual tensor-product sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
variable {T : Over (Spec (.of K))}

theorem poincareGraphBundle_parallelogram_class (a b : T ⟶ A.scheme) :
    Line.Bundles.LineBundle.classOf ((Bundles.poincareGraphBundle D p).pullback (a * b).left) *
      Line.Bundles.LineBundle.classOf ((Bundles.poincareGraphBundle D p).pullback (a * b⁻¹).left) =
      Line.Bundles.LineBundle.classOf ((Bundles.poincareGraphBundle D p).pullback a.left) ^ 2 *
        Line.Bundles.LineBundle.classOf ((Bundles.poincareGraphBundle D p).pullback b.left) ^ 2 := by
  have h (c : T ⟶ A.scheme) : Line.Bundles.LineBundle.classOf ((Bundles.poincareGraphBundle D p).pullback c.left) =
      D.poincarePairClass T (c ≫ p) c := Quotient.sound ⟨D.poincareGraphPullbackPairIso p c⟩
  simp only [h, MonObj.mul_comp, GrpObj.inv_comp]
  exact MultiplicativeBilinearParallelogram.multiplicativeBilinear_parallelogram (D.poincarePairClass T) (a ≫ p) (b ≫ p) a b

theorem poincareGraphBundle_parallelogram_iso (a b : T ⟶ A.scheme) :
    Nonempty ((((Bundles.poincareGraphBundle D p).pullback (a * b).left).tensor
      ((Bundles.poincareGraphBundle D p).pullback (a * b⁻¹).left)).sheaf ≅
      ((((Bundles.poincareGraphBundle D p).pullback a.left).tensorPower 2).tensor
        (((Bundles.poincareGraphBundle D p).pullback b.left).tensorPower 2)).sheaf) := by
  have he := poincareGraphBundle_parallelogram_class D p a b
  have ht : Line.Bundles.LineBundle.classOf ((((Bundles.poincareGraphBundle D p).pullback a.left).tensorPower 2).tensor
      (((Bundles.poincareGraphBundle D p).pullback b.left).tensorPower 2)) =
      Line.Bundles.LineBundle.classOf ((Bundles.poincareGraphBundle D p).pullback a.left) ^ 2 *
        Line.Bundles.LineBundle.classOf ((Bundles.poincareGraphBundle D p).pullback b.left) ^ 2 := by
    rw [Line.Bundles.LineBundle.classOf_tensor, Line.Bundles.LineBundle.classOf_tensorPower, Line.Bundles.LineBundle.classOf_tensorPower]
  exact Quotient.exact (he.trans ht.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.Parallelogram
