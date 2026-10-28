import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.PowerIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Powers

/-! # Power Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.PowerMultiplication

noncomputable section

/-! Every tensor power of the Poincare graph bundle satisfies the actual quadratic multiplication isomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
    (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]

def poincareGraphPower_multiplicationIso (m n : ℕ) :
    (((Bundles.poincareGraphBundle D p).tensorPower m).pullback (A.multiplication n).left).sheaf ≅
      ((Bundles.poincareGraphBundle D p).tensorPower (m * (n * n))).sheaf := by
  let L := Bundles.poincareGraphBundle D p
  exact Line.Bundles.LineBundle.powerBaseChangeIso (A.multiplication n).left L m ≪≫
    (TensorPower.Maps.tensorPowerFunctor A.scheme.left m).mapIso (PowerIsomorphism.poincareGraphBundle_multiplication_iso D p n).some ≪≫
    (L.tensorPowerComposeIso m (n * n)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.PowerMultiplication
