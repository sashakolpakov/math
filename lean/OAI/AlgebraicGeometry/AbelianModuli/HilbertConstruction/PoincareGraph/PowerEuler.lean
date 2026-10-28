import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.Euler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.PowerIsomorphism

/-! # Power Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.PowerEuler

noncomputable section

/-! The actual quadratic multiplication isomorphism gives the N-square Euler scaling law for a Poincare graph bundle. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem poincareGraphBundle_powerSquare_euler
    {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} [NeZero N]
    {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))} (D : Dual.Data.DualAbelianData A) (level : A.FullLevel N)
    (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p] (hN : (N : K) ≠ 0) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom ((Bundles.poincareGraphBundle D p).tensorPower (N * N)).sheaf =
      (N : ℤ) ^ (2 * g) * CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom (Bundles.poincareGraphBundle D p).sheaf :=
  (Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso A.scheme.hom
    (PowerIsomorphism.poincareGraphBundle_multiplication_iso D p N).some).symm.trans
      (D.fullLevel_multiplication_pullback_euler level (Bundles.poincareGraphBundle D p) hN)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.PowerEuler
