import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.OperatorAdapter
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.CrystallineFrobenius

/-! # Frobenius Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FrobeniusAdapter.CrystallineAdapter

noncomputable section

/-! Identify IntegralComparison's original small-site q-Frobenius with GeometricComparison's actual big-site Q_q operator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (q : ℕ) [Fact q.Prime]
  (X : Over (Spec (CommRingCat.of (ZMod q)))) [IsSeparated X.hom]

def nativeSmallToBigEquiv : IntegralComparison.Witt.Crystalline.rationalCohomology q (ZMod q) X 1
    ≃ₛₗ[(Crystalline.CoefficientAdapter.coefficientFieldEquiv q).toRingHom] Crystalline.CoefficientAdapter.RationalH1 q X :=
  (IntegralComparison.Global.CrystallineFrobenius.rationalEquiv q (ZMod q) X 1).symm.trans
    (Crystalline.CoefficientAdapter.coefficientTensorEquiv q (Crystalline.CoefficientAdapter.IntegralH1 q X))

theorem nativeSmallToBigEquiv_frobenius
    (x : IntegralComparison.Witt.Crystalline.rationalCohomology q (ZMod q) X 1) :
    nativeSmallToBigEquiv q X
        (IntegralComparison.Global.CrystallineFrobenius.rationalFrobenius q (ZMod q) X 1
          (by simp) 1 x) =
      Crystalline.CoefficientAdapter.rationalPullback q (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X)
        (nativeSmallToBigEquiv q X x) := by
  obtain ⟨y, rfl⟩ := (IntegralComparison.Global.CrystallineFrobenius.rationalEquiv q (ZMod q) X 1).surjective x
  have h := DFunLike.congr_fun
    (IntegralComparison.Global.CrystallineFrobenius.rational_intertwines q (ZMod q) X 1 (by simp) 1) y
  change IntegralComparison.Global.CrystallineFrobenius.rationalFrobenius q (ZMod q) X 1 (by simp) 1
      (IntegralComparison.Global.CrystallineFrobenius.rationalEquiv q (ZMod q) X 1 y) =
    IntegralComparison.Global.CrystallineFrobenius.rationalEquiv q (ZMod q) X 1
      (IntegralComparison.BigCrystallineFrobenius.rationalFrobenius q (ZMod q) X 1 (by simp) 1 y) at h
  rw [h]
  change Crystalline.CoefficientAdapter.coefficientTensorEquiv q (Crystalline.CoefficientAdapter.IntegralH1 q X)
      ((IntegralComparison.Global.CrystallineFrobenius.rationalEquiv q (ZMod q) X 1).symm
        (IntegralComparison.Global.CrystallineFrobenius.rationalEquiv q (ZMod q) X 1
          (IntegralComparison.BigCrystallineFrobenius.rationalFrobenius q (ZMod q) X 1 (by simp) 1 y))) =
    Crystalline.CoefficientAdapter.rationalPullback q (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X)
      (Crystalline.CoefficientAdapter.coefficientTensorEquiv q (Crystalline.CoefficientAdapter.IntegralH1 q X)
        ((IntegralComparison.Global.CrystallineFrobenius.rationalEquiv q (ZMod q) X 1).symm
          (IntegralComparison.Global.CrystallineFrobenius.rationalEquiv q (ZMod q) X 1 y)))
  erw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact Crystalline.OperatorAdapter.CrystallineAdapter.coefficientEquiv_frobenius q X y

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FrobeniusAdapter.CrystallineAdapter
