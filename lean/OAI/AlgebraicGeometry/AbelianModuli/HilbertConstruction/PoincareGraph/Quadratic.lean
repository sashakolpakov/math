import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PairNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PairClass
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Quadratic -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.Quadratic

noncomputable section

/-! A Poincare graph bundle attached to a homomorphism is symmetric and scales quadratically under multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]

theorem poincareGraphBundle_symmetric :
    Nonempty (((Bundles.poincareGraphBundle D p).pullback ι[A.scheme].left).sheaf ≅
      (Bundles.poincareGraphBundle D p).sheaf) := by
  have hp : ι[A.scheme] ≫ p = p⁻¹ := by rw [GrpObj.inv_hom, ← Hom.inv_def]
  have he : Line.Bundles.LineBundle.classOf (D.poincarePair (ι[A.scheme] ≫ p) ι[A.scheme]) =
      Line.Bundles.LineBundle.classOf (D.poincarePair p (𝟙 A.scheme)) := by
    rw [hp, GrpObj.inv_eq_inv]
    exact D.poincarePairClass_inv_inv A.scheme p (𝟙 A.scheme)
  have hc : Line.Bundles.LineBundle.classOf ((Bundles.poincareGraphBundle D p).pullback ι[A.scheme].left) =
      Line.Bundles.LineBundle.classOf (D.poincarePair (ι[A.scheme] ≫ p) ι[A.scheme]) :=
    Quotient.sound ⟨D.poincareGraphPullbackPairIso p ι[A.scheme]⟩
  have h : Line.Bundles.LineBundle.classOf ((Bundles.poincareGraphBundle D p).pullback ι[A.scheme].left) =
      Line.Bundles.LineBundle.classOf (Bundles.poincareGraphBundle D p) :=
    hc.trans (he.trans (Quotient.sound ⟨D.poincarePairGraphIso p⟩))
  exact Quotient.exact h

theorem poincareGraphBundle_multiplication_class (n : ℕ) :
    Line.Bundles.LineBundle.classOf ((Bundles.poincareGraphBundle D p).pullback (A.multiplication n).left) =
      Line.Bundles.LineBundle.classOf (Bundles.poincareGraphBundle D p) ^ (n * n) := by
  have hp : A.multiplication n ≫ p = p ^ n := by
    simp only [Abelian.Schemes.AbelianScheme.multiplication, MonObj.pow_comp, Category.id_comp]
  have he : Line.Bundles.LineBundle.classOf (D.poincarePair (A.multiplication n ≫ p) (A.multiplication n)) =
      Line.Bundles.LineBundle.classOf (D.poincarePair p (𝟙 A.scheme)) ^ (n * n) := by
    rw [hp]
    exact D.poincarePairClass_pow A.scheme p (𝟙 A.scheme) n n
  have hc : Line.Bundles.LineBundle.classOf ((Bundles.poincareGraphBundle D p).pullback (A.multiplication n).left) =
      Line.Bundles.LineBundle.classOf (D.poincarePair (A.multiplication n ≫ p) (A.multiplication n)) :=
    Quotient.sound ⟨D.poincareGraphPullbackPairIso p (A.multiplication n)⟩
  exact hc.trans
    (he.trans (congrArg (fun q : Line.Bundles.LineBundle.IsoClass A.scheme.left => q ^ (n * n))
      (Quotient.sound ⟨D.poincarePairGraphIso p⟩)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.Quadratic
