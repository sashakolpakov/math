import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.Quadratic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Classes

/-! # Power Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.PowerIsomorphism

noncomputable section

/-! The quadratic multiplication law as an isomorphism of actual tensor-power sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]

theorem poincareGraphBundle_multiplication_iso (n : ℕ) :
    Nonempty (((Bundles.poincareGraphBundle D p).pullback (A.multiplication n).left).sheaf ≅
      ((Bundles.poincareGraphBundle D p).tensorPower (n * n)).sheaf) :=
  Line.Bundles.LineBundle.iso_tensorPower_of_class_eq _ _ (n * n) (Quadratic.poincareGraphBundle_multiplication_class D p n)

theorem poincareGraphBundle_multiplication_isTensorPower (n : ℕ) :
    Tensor.Powers.IsTensorPower (Bundles.poincareGraphBundle D p).sheaf (n * n)
      (((Bundles.poincareGraphBundle D p).pullback (A.multiplication n).left).sheaf) :=
  ((Bundles.poincareGraphBundle D p).tensorPower_isTensorPower (n * n)).of_targetIso
    (poincareGraphBundle_multiplication_iso D p n).some.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.PowerIsomorphism
