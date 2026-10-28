import OAI.NumberTheory.PadicHodge.GeometricComparison.FrobeniusAdapter
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.CoefficientAdapter

/-! # Operator Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.OperatorAdapter.CrystallineAdapter

noncomputable section

/-! Native crystalline operators under the canonical split coefficient change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (q : ℕ) [Fact q.Prime]

def fractionPullback {X Y : Over (Spec (CommRingCat.of (ZMod q)))} (f : X ⟶ Y) :
    FractionRing (CoefficientAdapter.Witt q) ⊗[CoefficientAdapter.Witt q] CoefficientAdapter.IntegralH1 q Y →ₗ[
      FractionRing (CoefficientAdapter.Witt q)]
    FractionRing (CoefficientAdapter.Witt q) ⊗[CoefficientAdapter.Witt q] CoefficientAdapter.IntegralH1 q X :=
  (CoefficientAdapter.integralPullback (p := q) (J := Ideal.span {(q : CoefficientAdapter.Witt q)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
    f.left (by simp only [CoefficientAdapter.wittStructure, ← Category.assoc, Over.w]) 1).baseChange
      (FractionRing (CoefficientAdapter.Witt q))

theorem coefficientEquiv_pullback {X Y : Over (Spec (CommRingCat.of (ZMod q)))} (f : X ⟶ Y)
    (x : FractionRing (CoefficientAdapter.Witt q) ⊗[CoefficientAdapter.Witt q] CoefficientAdapter.IntegralH1 q Y) :
    CoefficientAdapter.coefficientTensorEquiv q (CoefficientAdapter.IntegralH1 q X) (fractionPullback q f x) =
      CoefficientAdapter.rationalPullback q f
        (CoefficientAdapter.coefficientTensorEquiv q (CoefficientAdapter.IntegralH1 q Y) x) :=
  CoefficientAdapter.coefficientTensorEquiv_map q (CoefficientAdapter.IntegralH1 q Y)
    (CoefficientAdapter.integralPullback (p := q) (J := Ideal.span {(q : CoefficientAdapter.Witt q)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
      f.left (by simp only [CoefficientAdapter.wittStructure, ← Category.assoc, Over.w]) 1) x

variable (X : Over (Spec (CommRingCat.of (ZMod q))))

theorem fractionFrobenius_eq :
    IntegralComparison.BigCrystallineFrobenius.rationalFrobenius q (ZMod q) X 1
      (by rw [ZMod.card, pow_one]) 1 =
      fractionPullback q (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X) := by
  have h : IntegralComparison.BigCrystallineFrobenius.integralFrobenius q (ZMod q) X 1
      (by rw [ZMod.card, pow_one]) 1 =
      CoefficientAdapter.integralPullback (p := q) (J := Ideal.span {(q : CoefficientAdapter.Witt q)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
        (f := CoefficientAdapter.wittStructure q X) (fY := CoefficientAdapter.wittStructure q X)
        (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X).left
        (by simp only [CoefficientAdapter.wittStructure, ← Category.assoc, Over.w]) 1 :=
    LinearMap.ext (FrobeniusAdapter.CrystallineAdapter.integralFrobenius_eq q X 1)
  exact congrArg (LinearMap.baseChange (FractionRing (CoefficientAdapter.Witt q))) h

theorem coefficientEquiv_frobenius
    (x : IntegralComparison.BigCrystallineFrobenius.RationalCohomology q (ZMod q) X 1) :
    CoefficientAdapter.coefficientTensorEquiv q (CoefficientAdapter.IntegralH1 q X)
        (IntegralComparison.BigCrystallineFrobenius.rationalFrobenius q (ZMod q) X 1
          (by rw [ZMod.card, pow_one]) 1 x) =
      CoefficientAdapter.rationalPullback q (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X)
        (CoefficientAdapter.coefficientTensorEquiv q (CoefficientAdapter.IntegralH1 q X) x) := by
  rw [fractionFrobenius_eq]
  exact coefficientEquiv_pullback q (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X) x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.OperatorAdapter.CrystallineAdapter
