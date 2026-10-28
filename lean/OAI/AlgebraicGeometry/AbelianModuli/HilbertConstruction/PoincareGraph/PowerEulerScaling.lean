import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.PowerEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.PowerMultiplication

/-! # Power Euler Scaling -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.PowerEulerScaling

noncomputable section

/-! Genuine Euler characteristic of every graph-bundle tensor power obeys the full-level N-square scaling law. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem poincareGraphBundle_tensorPowers_euler_scaling
    {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} [NeZero N]
    {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))} (D : Dual.Data.DualAbelianData A) (level : A.FullLevel N)
    (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p] (hN : (N : K) ≠ 0) (m : ℕ) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom
      ((Bundles.poincareGraphBundle D p).tensorPower (m * (N * N))).sheaf =
      (N : ℤ) ^ (2 * g) * CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom
        ((Bundles.poincareGraphBundle D p).tensorPower m).sheaf :=
  (Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso A.scheme.hom
    (PowerMultiplication.poincareGraphPower_multiplicationIso D p m N)).symm.trans
      (D.fullLevel_multiplication_pullback_euler level ((Bundles.poincareGraphBundle D p).tensorPower m) hN)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.PowerEulerScaling
