import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullbackCoherence

/-! # Integral Composition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.IntegralComposition

noncomputable section

/-! Composition on the actual integral big crystalline cohomology, before scalar extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {p : ℕ} {B : Type} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y Z : Scheme} {fX : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)} {fZ : Z ⟶ Spec (CommRingCat.of B)}

theorem integralPullback_comp (g : X ⟶ Y) (hg : g ≫ fY = fX)
    (h : Y ⟶ Z) (hh : h ≫ fZ = fY) (n : ℕ) (x : CoefficientAdapter.IntegralCohomology p B J δ fZ n) :
    CoefficientAdapter.integralPullback g hg n (CoefficientAdapter.integralPullback h hh n x) =
      CoefficientAdapter.integralPullback (g ≫ h) (by rw [Category.assoc, hh, hg]) n x :=
  PeriodInvariants.CrystallinePullbackCoherence.Big.pullback_comp g hg h hh n x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.IntegralComposition
