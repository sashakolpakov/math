import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IdealCoefficientTests
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.PullbackVanishing

/-! # Ideal Coefficient Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IdealCoefficientBaseChange

noncomputable section

/-! Coefficient ideals for flat sources commute with every affine
base change, including non-Noetherian test algebras. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {R A : CommRingCat.{u}} {X : Scheme.{u}}
variable (f : X ⟶ Spec R) [Flat f] (K : X.IdealSheafData)
variable (I : Ideal R) (hI : IdealCoefficientTests.IsAffineIdealCoefficient R f K I)
include hI

theorem affineIdealCoefficient_baseChange (φ : R ⟶ A) :
    IdealCoefficientTests.IsAffineIdealCoefficient A (pullback.snd f (Spec.map φ))
      (K.comap (pullback.fst f (Spec.map φ))) (I.map φ.hom) := by
  apply IdealCoefficientTests.affineIdealCoefficient_of_tests
  intro B ψ
  rw [Presentations.Ideal.PullbackVanishing.pullback_ideal_vanishing_comp, ← Spec.map_comp,
    IdealCoefficientTests.affineIdealCoefficient_test R f K I hI,
    Ideal.map_le_iff_le_comap, RingHom.comap_ker]
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IdealCoefficientBaseChange
