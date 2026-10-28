import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCrystallineCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCrystallineEquiv
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallinePullbackCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralReductionCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineInverseLimitProjection

/-! # Crystalline Restriction Ext -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction

/-! The original bounded crystalline restriction of the constructed
integral comparison is precisely native principal reduction in p-adic coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))
  (hprojective : IntegralComparison.Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "D" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientDescent.restrict p

def bounded (n : ℕ) : ModuleCat.{2} ℤ_[p] :=
  (D).obj (ModuleCat.of R (IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w n 1))

def restriction (n : ℕ) : CrystallinePullbackCoordinates.IntrinsicPadicCrystallineScalarCoordinates.integral p Y →ₗ[ℤ_[p]] bounded p Y n :=
  ((D).map (ModuleCat.ofHom (IntegralComparison.BoundedCrystalline.CrystallineCohomology.restriction w n 1))).hom

def finiteEquiv (n : ℕ) : CochainQuotientCohomology.PrincipalCochainQuotient.cohomology ℤ_[p] K (p : ℤ_[p]) (n + 1) 1 ≃ₗ[ℤ_[p]]
    bounded p Y n :=
  (Coefficient.IntrinsicPadicCoefficientDescent.equiv p ((PrincipalCochainExact.PrincipalCochainQuotient.quotient ℤ_[p] K (p : ℤ_[p]) (n + 1)).homology 1)).trans
    (((D).mapIso (PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel.iso p X Y f hp I n)).toLinearEquiv)

theorem square (n : ℕ) : (restriction p Y n).comp
    (IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv.equiv p X Y f hp I hprojective).toLinearMap =
      (finiteEquiv p X Y f hp I n).toLinearMap.comp (IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X (n + 1)) := by
  have h := congrArg (D).map (IntegralCrystallineCoordinates.IntrinsicPadicIntegralCrystallineCoordinates.comparison_projection p X Y f hp I hprojective n)
  simp only [Functor.map_comp] at h
  apply LinearMap.ext
  intro x
  let y := IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.equiv p X x
  have h' := ConcreteCategory.congr_hom h (Coefficient.IntrinsicPadicCoefficientDescent.equiv p ((K).homology 1) y)
  exact h'.trans (congrArg (fun z => (D).map (PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel.iso p X Y f hp I n).hom z)
    (Coefficient.IntrinsicPadicCoefficientDescent.natural p
      (ModuleCat.ofHom (CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] K (p : ℤ_[p]) (n + 1) 1)) y).symm)

theorem zero_iff (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1) :
    restriction p Y n (IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv.equiv p X Y f hp I hprojective x) = 0 ↔
      IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X (n + 1) x = 0 := by
  have h := LinearMap.congr_fun (square p X Y f hp I hprojective n) x
  constructor
  · intro hx
    apply (finiteEquiv p X Y f hp I n).injective
    exact (h.symm.trans hx).trans (map_zero (finiteEquiv p X Y f hp I n)).symm
  · intro hx
    exact h.trans ((congrArg (finiteEquiv p X Y f hp I n) hx).trans
      (map_zero (finiteEquiv p X Y f hp I n)))

theorem zero_iff_prime_multiple (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1) :
    restriction p Y 0 (IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv.equiv p X Y f hp I hprojective x) = 0 ↔
      ∃ y, x = (p : ℤ_[p]) • y :=
  (zero_iff p X Y f hp I hprojective 0 x).trans (IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.zero_iff p X x)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineRestrictionExt.IntrinsicPadicCrystallineRestrictionExt

/-! Original bounded restrictions jointly detect equality in the
actual p-adic integral crystalline module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (hprojective : IntegralComparison.Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

include hprojective

theorem zero (x : CrystallinePullbackCoordinates.IntrinsicPadicCrystallineScalarCoordinates.integral p Y)
    (hx : ∀ n, IntrinsicPadicIntegralCrystallineReduction.restriction p Y n x = 0) : x = 0 := by
  let := IntegralComparison.SmoothProper.CrystallineInverseLimit.inclusion_mono p (ZMod p) Y hprojective 1
  exact IntegralComparison.Crystalline.RestrictionJointKernel.zero_of_restrictions w 1 x hx

theorem ext (x y : CrystallinePullbackCoordinates.IntrinsicPadicCrystallineScalarCoordinates.integral p Y)
    (h : ∀ n, IntrinsicPadicIntegralCrystallineReduction.restriction p Y n x =
      IntrinsicPadicIntegralCrystallineReduction.restriction p Y n y) : x = y := by
  apply sub_eq_zero.mp
  apply zero p Y hprojective (x - y)
  intro n
  rw [map_sub, h n, sub_self]

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineRestrictionExt.IntrinsicPadicCrystallineRestrictionExt

end

end OAI
