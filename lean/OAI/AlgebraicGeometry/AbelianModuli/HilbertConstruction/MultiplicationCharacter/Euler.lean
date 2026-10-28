import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicationCharacter.Homogeneity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BundleEuler

/-! # Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual multiplication-character line bundles preserve genuine Euler characteristic under tensor product. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem Dual.Data.DualAbelianData.multiplicationCharacter_twist_euler {K : Type u} [Field K] [IsAlgClosed K]
    {g N : ℕ} [NeZero N] {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))} (D : Dual.Data.DualAbelianData A)
    (level : A.FullLevel N) (L : Line.Bundles.LineBundle A.scheme.left)
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom
      (L.tensor (A.multiplicationCharacterLineBundle level χ hN)).sheaf =
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom L.sheaf :=
  D.homogeneousBundle_twist_euler L (A.multiplicationCharacterLineBundle level χ hN)
    (A.multiplicationCharacterLineBundle_homogeneous level χ hN)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
