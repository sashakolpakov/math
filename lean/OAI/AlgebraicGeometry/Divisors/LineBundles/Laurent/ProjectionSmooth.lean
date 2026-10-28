import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.Smooth
import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.FiberGenericPoint
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Projection Smooth -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.ProjectionSmooth.BundleCycles

noncomputable section

/-! The actual punctured affine line is smooth over its coefficient ring. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem laurent_smooth (R : Type) [CommRing R] : Algebra.Smooth R (LaurentPolynomial R) := by
  let : IsScalarTower R (Polynomial R) (LaurentPolynomial R) := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    exact (Polynomial.toLaurent_C r).symm
  let : Algebra.FinitePresentation (Polynomial R) (LaurentPolynomial R) :=
    IsLocalization.Away.finitePresentation (Polynomial.X : Polynomial R)
  exact ⟨Laurent.Smooth.BundleCycles.laurent_formallySmooth R R, Algebra.FinitePresentation.trans R (Polynomial R) _⟩

instance laurentProjection_smooth (R : Type) [CommRing R] : Smooth (FiberGenericPoint.BundleCycles.laurentProjection R) := by
  let : Algebra.Smooth R (LaurentPolynomial R) := laurent_smooth R
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.ProjectionSmooth.BundleCycles
