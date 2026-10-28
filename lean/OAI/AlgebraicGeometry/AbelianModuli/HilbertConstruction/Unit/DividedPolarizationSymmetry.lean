import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DividedPolarizationSymmetry
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.GroupDivisionLocus

/-! # Divided Polarization Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.DividedPolarizationSymmetry

noncomputable section

/-! Symmetry of a divisor of an inducing homomorphism when the dividing
integer is invertible on the base field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem unit_divisor_pair_symmetric
    {K : Type} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
    (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
    (n : ℕ) (hnUnit : IsUnit (n : Γ(Spec (.of K), ⊤)))
    (m : A.scheme ⟶ D.abelian.scheme) (L : Line.Bundles.LineBundle A.scheme.left)
    (e : (((D.poincareAt m).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
      (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)
    (hp : A.multiplication n ≫ p = m)
    {T : Over (Spec (.of K))} (a b : T ⟶ A.scheme) :
    D.poincarePairClass T (a ≫ p) b = D.poincarePairClass T (b ≫ p) a := by
  have hg := GroupDivisionLocus.unit_multiplication_geometry A n hnUnit
  let : Flat (A.multiplication n).left := hg.2.1
  let : Surjective (A.multiplication n).left := hg.2.2.1
  let : LocallyOfFinitePresentation (A.multiplication n).left := hg.2.2.2.1
  have hscalar : A.multiplication n ≫ p = p ^ n := by
    change ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n) ≫ p = p ^ n
    rw [MonObj.pow_comp, Category.id_comp]
  have hm : p ^ n = m := hscalar.symm.trans hp
  refine DividedPolarizationSymmetry.poincarePairClass_symmetric_of_multiple D p n ?_ a b
  intro x y
  rw [hm]
  exact Polarization.PairSymmetry.polarizationPairClass_symmetric D m L e x y

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.DividedPolarizationSymmetry
