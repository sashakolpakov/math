import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.RelativePicardInjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.TensorNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.PicardSmoothCompatibility

/-! # Multiplication Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The Poincare multiplication formula is an actual line-bundle isomorphism over arbitrary test schemes over a field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}

theorem Dual.Data.DualAbelianData.poincareAt_mul_iso_overField (D : Dual.Data.DualAbelianData A)
    {T : Over (Spec (.of K))} (x y : T ⟶ D.abelian.scheme) :
    Nonempty ((D.poincareAt (x * y)).sheaf ≅ ((D.poincareAt x).tensor (D.poincareAt y)).sheaf) := by
  have : IsReduced A.scheme.left := A.reduced_overField
  have : ConnectedSpace A.scheme.left := A.connected_overField
  exact Proper.RelativePicardInjectivity.properField_bundleIso_of_relativePicard_eq A.scheme η[A.scheme].left η[A.scheme].w T
    (D.poincareAt (x * y)) ((D.poincareAt x).tensor (D.poincareAt y))
    (A.familyZeroSection T) (A.familyZeroSection_fst T)
    (D.poincareAt_zeroIso (x * y) ≪≫ (D.poincareAt_tensor_zeroIso x y).symm)
    (D.poincareAt_mul_class_overField x y)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
