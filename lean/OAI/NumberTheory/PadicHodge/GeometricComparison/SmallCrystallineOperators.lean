import OAI.NumberTheory.PadicHodge.GeometricComparison.GlobalCrystallineAdapter
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.OperatorAdapter
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.Separation

/-! # Small Crystalline Operators -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineOperators.CrystallineAdapter

noncomputable section

/-! Native Cohomology small-site pullback and Frobenius, through the proved big-site comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (q : ℕ) [Fact q.Prime]
variable (X : Over (Spec (CommRingCat.of (ZMod q)))) [IsSeparated X.hom]

/-- The native Cohomology fraction-field cohomology and GeometricComparison's big-site Q_q cohomology agree
semilinearly for the canonical coefficient-field identification. -/
def smallToBigEquiv : AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology q (ZMod q) X 1
    ≃ₛₗ[(Crystalline.CoefficientAdapter.coefficientFieldEquiv q).toRingHom] Crystalline.CoefficientAdapter.RationalH1 q X :=
  (GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) X 1).symm.trans
    (Crystalline.CoefficientAdapter.coefficientTensorEquiv q (Crystalline.CoefficientAdapter.IntegralH1 q X))

variable {X} {Y : Over (Spec (CommRingCat.of (ZMod q)))} [IsSeparated Y.hom]

/-- Pullback by the actual scheme map on Cohomology's independently defined small-site cohomology. -/
def smallPullback (f : X ⟶ Y) :
    AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology q (ZMod q) Y 1 →ₗ[FractionRing (Crystalline.CoefficientAdapter.Witt q)]
      AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology q (ZMod q) X 1 :=
  (GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) X 1).toLinearMap.comp
    ((Crystalline.OperatorAdapter.CrystallineAdapter.fractionPullback q f).comp (GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) Y 1).symm.toLinearMap)

theorem rationalEquiv_pullback (f : X ⟶ Y)
    (x : FractionRing (Crystalline.CoefficientAdapter.Witt q) ⊗[Crystalline.CoefficientAdapter.Witt q] Crystalline.CoefficientAdapter.IntegralH1 q Y) :
    smallPullback q f (GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) Y 1 x) =
      GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) X 1 (Crystalline.OperatorAdapter.CrystallineAdapter.fractionPullback q f x) := by
  change GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) X 1
    (Crystalline.OperatorAdapter.CrystallineAdapter.fractionPullback q f ((GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) Y 1).symm
      (GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) Y 1 x))) = _
  erw [LinearEquiv.symm_apply_apply]

theorem smallToBigEquiv_pullback (f : X ⟶ Y)
    (x : AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology q (ZMod q) Y 1) :
    smallToBigEquiv q X (smallPullback q f x) =
      Crystalline.CoefficientAdapter.rationalPullback q f (smallToBigEquiv q Y x) := by
  change Crystalline.CoefficientAdapter.coefficientTensorEquiv q (Crystalline.CoefficientAdapter.IntegralH1 q X)
    ((GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) X 1).symm
      (GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) X 1 (Crystalline.OperatorAdapter.CrystallineAdapter.fractionPullback q f
        ((GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) Y 1).symm x)))) = _
  erw [LinearEquiv.symm_apply_apply]
  exact Crystalline.OperatorAdapter.CrystallineAdapter.coefficientEquiv_pullback q f ((GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) Y 1).symm x)

variable (X)

def smallFrobenius : Module.End (FractionRing (Crystalline.CoefficientAdapter.Witt q))
    (AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology q (ZMod q) X 1) :=
  smallPullback q (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X)

theorem smallToBigEquiv_frobenius
    (x : AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology q (ZMod q) X 1) :
    smallToBigEquiv q X (smallFrobenius q X x) =
      Crystalline.CoefficientAdapter.rationalPullback q (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X)
        (smallToBigEquiv q X x) :=
  smallToBigEquiv_pullback q (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X) x

theorem rationalEquiv_frobenius
    (x : IntegralComparison.BigCrystallineFrobenius.RationalCohomology q (ZMod q) X 1) :
    smallFrobenius q X (GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) X 1 x) =
      GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) X 1
        (IntegralComparison.BigCrystallineFrobenius.rationalFrobenius q (ZMod q) X 1
          (by rw [ZMod.card, pow_one]) 1 x) := by
  rw [Crystalline.OperatorAdapter.CrystallineAdapter.fractionFrobenius_eq]
  exact rationalEquiv_pullback q (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X) x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineOperators.CrystallineAdapter
