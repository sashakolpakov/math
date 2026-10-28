import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison
import OAI.AlgebraicGeometry.Albanese.Construction.Rigidity
import OAI.AlgebraicGeometry.AbelianScheme.HomExtensionLocalRings

/-! # Dual -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Dual

noncomputable section

/-! The represented dual maps preserve the actual group law. Over a
geometric field this follows from their proved origin property and rigidity
of abelian varieties. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison

variable {K : Type u} [Field K] [IsAlgClosed K] {a b : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of K))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b (Spec (.of K))}

omit [IsAlgClosed K] in
theorem abelian_product_integral (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of K))) :
    IsIntegral (A.scheme ⊗ A.scheme).left := by
  have : Smooth (A.scheme ⊗ A.scheme).hom := by dsimp; infer_instance
  have : IsProper (A.scheme ⊗ A.scheme).hom := by dsimp; infer_instance
  have : GeometricallyConnected (A.scheme ⊗ A.scheme).hom :=
    GeometricallyConnected.comp (CategoryTheory.Limits.pullback.fst _ _) A.scheme.hom
  exact AbelianScheme.HomExtensionLocalRings.LocalRings.integral_of_smooth_proper_connected
    (A.scheme ⊗ A.scheme).hom

theorem dualMap_isMonHom (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] : IsMonHom (DualComparison.dualMap DA DB f) := by
  have : IsIntegral (DB.abelian.scheme ⊗ DB.abelian.scheme).left :=
    abelian_product_integral DB.abelian
  apply Albanese.Construction.Rigidity.isMonHom_of_pointed_of_integral_product DB.abelian.scheme DA.abelian.scheme
  simpa only [MonObj.one_eq_one] using DualComparison.dualMap_origin DA DB f (𝟙_ _)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Dual
