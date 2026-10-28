import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IdealCoefficientTests
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentOpenLocality

/-! # Coefficient Open Cover -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.CoefficientOpenCover

noncomputable section

/-! Coefficient ideals from an open cover of the source combine by sum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem affineIdealCoefficient_of_openCover (R : CommRingCat.{u})
    {X : Scheme.{u}} (f : X ⟶ Spec R) (K : X.IdealSheafData)
    (U : X.OpenCover.{v}) (I : U.I₀ → Ideal R)
    (hI : ∀ i, IdealCoefficientTests.IsAffineIdealCoefficient R (U.f i ≫ f) (K.comap (U.f i)) (I i)) :
    IdealCoefficientTests.IsAffineIdealCoefficient R f K (⨆ i, I i) := by
  intro J
  rw [Presentations.Ideal.ContainmentOpenLocality.ideal_le_iff_openCover U, iSup_le_iff]
  apply forall_congr'
  intro i
  rw [← Scheme.IdealSheafData.comap_comp]
  exact hI i J

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.CoefficientOpenCover
