import OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.CrystallineCupNaturality

/-! # Crystalline Bounded Scalar -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.CrystallineBoundedScalar

noncomputable section

/-! Scalar action on every original bounded crystalline group is
detected on integral and rational crystalline cohomology. No choices
of finite-level lifts or traces need compatibility with each other. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CrystallineCup

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hX : Projectivity.Construction.ProjectiveOver k X.hom) (f : X ⟶ X) (i d : ℕ)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "hf" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricRefinement.over_witt p k X X f
local notation "W" => WittVector p k
local notation "F" => FractionRing (WittVector p k)

variable (h : ∀ (n : ℕ) (x : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k X) n i), BoundedCrystalline.CrystallinePullback.pullback f.left
    (SmoothProper.WittGeometricRefinement.over_witt p k X X f) n i x = d • x)

include h hX in
theorem integral_scalar (x : Witt.Crystalline.integralCohomology p k X i) :
    Integral.CrystallineCupNaturality.pullback p k X X f i x = d • x := by
  apply (Integral.CrystallineCup.equivalence p k X hX i).injective
  apply Subtype.ext
  funext n
  rw [Integral.CrystallineCup.equivalence_coordinate, Integral.CrystallineCup.equivalence_coordinate,
    Integral.CrystallineCupNaturality.restriction_pullback, h, map_nsmul]

include h hX in
theorem original_integral_scalar (x : Witt.Crystalline.integralCohomology p k X i) :
    PeriodInvariants.CrystallinePullback.integralPullback p k f i x = d • x := by
  rw [← CrystallineCupNaturality.integralPullback_eq]
  exact integral_scalar p k X hX f i d h x

include h hX in
theorem rational_scalar (x : Witt.Crystalline.rationalCohomology p k X i) :
    PeriodInvariants.CrystallinePullback.rationalPullback p k f i x = d • x := by
  change (PeriodInvariants.CrystallinePullback.integralPullback p k f i).baseChange F x = d • x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul a x =>
      rw [LinearMap.baseChange_tmul, original_integral_scalar p k X hX f i d h]
      exact map_nsmul (TensorProduct.mk W F (Witt.Crystalline.integralCohomology p k X i) a) d x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.CrystallineBoundedScalar
