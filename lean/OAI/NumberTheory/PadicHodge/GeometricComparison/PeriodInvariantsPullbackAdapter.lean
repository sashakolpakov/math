import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineOperators
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullback

/-! # Period Invariants Pullback Adapter -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.PeriodInvariantsPullbackAdapter.CrystallineAdapter

/-! Identify independently defined crystalline pullbacks through the actual big/small comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (q : ℕ) [Fact q.Prime]
  (X : Over (Spec (CommRingCat.of (ZMod q)))) [IsSeparated X.hom]

def nativeBigSmallEquiv :
    (FractionRing (Crystalline.CoefficientAdapter.Witt q) ⊗[Crystalline.CoefficientAdapter.Witt q] Crystalline.CoefficientAdapter.IntegralH1 q X) ≃ₗ[
      FractionRing (Crystalline.CoefficientAdapter.Witt q)] IntegralComparison.Witt.Crystalline.rationalCohomology q (ZMod q) X 1 :=
  (IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt q (ZMod q) X 1).baseChange
    (Crystalline.CoefficientAdapter.Witt q) (FractionRing (Crystalline.CoefficientAdapter.Witt q)) _ _

theorem rationalEquiv_factor
    (x : FractionRing (Crystalline.CoefficientAdapter.Witt q) ⊗[Crystalline.CoefficientAdapter.Witt q] Crystalline.CoefficientAdapter.IntegralH1 q X) :
    GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) X 1 x =
      SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.rationalEquiv 1 (nativeBigSmallEquiv q X x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy =>
      calc
        _ = GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) X 1 x + GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) X 1 y :=
          (GlobalCrystallineAdapter.CrystallineAdapter.rationalEquiv q (ZMod q) X 1).map_add x y
        _ = _ := congrArg₂ (· + ·) hx hy
        _ = _ := by simp only [map_add]

variable {X} {Y : Over (Spec (CommRingCat.of (ZMod q)))} [IsSeparated Y.hom]

theorem nativeBigSmallEquiv_pullback (f : X ⟶ Y)
    (x : FractionRing (Crystalline.CoefficientAdapter.Witt q) ⊗[Crystalline.CoefficientAdapter.Witt q] Crystalline.CoefficientAdapter.IntegralH1 q Y) :
    PeriodInvariants.CrystallinePullback.rationalPullback q (ZMod q) f 1 (nativeBigSmallEquiv q Y x) =
      nativeBigSmallEquiv q X (Crystalline.OperatorAdapter.CrystallineAdapter.fractionPullback q f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      change a ⊗ₜ[Crystalline.CoefficientAdapter.Witt q]
        (IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt q (ZMod q) X 1
          (PeriodInvariants.CrystallinePullback.bigPullback q (ZMod q) f 1
            ((IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt q (ZMod q) Y 1).symm
              (IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt q (ZMod q) Y 1 x)))) = _
      erw [LinearEquiv.symm_apply_apply]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem smallPullback_eq_native (f : X ⟶ Y)
    (x : IntegralComparison.Witt.Crystalline.rationalCohomology q (ZMod q) Y 1) :
    SmallCrystallineOperators.CrystallineAdapter.smallPullback q f (SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.rationalEquiv 1 x) =
      SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.rationalEquiv 1
        (PeriodInvariants.CrystallinePullback.rationalPullback q (ZMod q) f 1 x) := by
  obtain ⟨y, rfl⟩ := (nativeBigSmallEquiv q Y).surjective x
  rw [← rationalEquiv_factor, SmallCrystallineOperators.CrystallineAdapter.rationalEquiv_pullback, nativeBigSmallEquiv_pullback,
    ← rationalEquiv_factor]

end NumberTheory.PadicHodge.GeometricComparison.PeriodInvariantsPullbackAdapter.CrystallineAdapter

namespace NumberTheory.PadicHodge.GeometricComparison.PeriodInvariantsPullbackAdapter

/-! An explicit equality for independently defined small crystalline pullback operators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem operator_eq_conjugate {V V' W W' : Type*} (eX : V' ≃ W') (eY : V ≃ W)
    (T : W → W') (U : V → V')
    (h : ∀ x, T (eY x) = eX (U x)) (x : W) : T x = eX (U (eY.symm x)) := by
  simpa only [eY.apply_symm_apply] using h (eY.symm x)

namespace CrystallineAdapter

variable (q : ℕ) [Fact q.Prime]
  {X Y : Over (Spec (CommRingCat.of (ZMod q)))} [IsSeparated X.hom] [IsSeparated Y.hom]

theorem smallPullback_eq_native_conjugate (f : X ⟶ Y) :
    SmallCrystallineOperators.CrystallineAdapter.smallPullback q f = (SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.rationalEquiv (p := q) (k := ZMod q) (X := X) 1).toLinearMap.comp
      ((PeriodInvariants.CrystallinePullback.rationalPullback q (ZMod q) f 1).comp
        (SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.rationalEquiv (p := q) (k := ZMod q) (X := Y) 1).symm.toLinearMap) := by
  apply LinearMap.ext
  exact operator_eq_conjugate
    (SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.rationalEquiv (p := q) (k := ZMod q) (X := X) 1).toEquiv
    (SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.rationalEquiv (p := q) (k := ZMod q) (X := Y) 1).toEquiv
    (SmallCrystallineOperators.CrystallineAdapter.smallPullback q f) (PeriodInvariants.CrystallinePullback.rationalPullback q (ZMod q) f 1)
    (smallPullback_eq_native q f)

end CrystallineAdapter

end NumberTheory.PadicHodge.GeometricComparison.PeriodInvariantsPullbackAdapter

end

end OAI
