import OAI.NumberTheory.PadicHodge.WeakAdmissibility.Coordinates
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DividedPowerCompletion
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.BoundedCompletion
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.Comparison

/-! # Finite Series Comparison -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteSeriesComparison

noncomputable section

/-! The actual finite comparison is evaluation of the restricted divided-power coefficients. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaQuotients OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaDividedPowers
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteDeRhamP OAI.NumberTheory.PadicHodge.WeakAdmissibility.DenominatorBound OAI.NumberTheory.PadicHodge.WeakAdmissibility.Comparison OAI.NumberTheory.PadicHodge.WeakAdmissibility.DividedPowerCompletion
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Coordinates OAI.NumberTheory.PadicHodge.WeakAdmissibility.BoundedCompletion.ModuleComparison
variable (p : ℕ) [Fact p.Prime]

abbrev CoefficientCompletion := AdicCompletion (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (ℕ →₀ Logarithm.PeriodRings.AInf p)

def finiteTerm (m n : ℕ) : Logarithm.PeriodRings.AInf p →+ FiniteDeRhamP.FiniteDeRham p m where
  toFun a := FiniteDeRhamP.uncompletedToFinite p m
    (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) a * ThetaDividedPowers.thetaDividedPower p n)
  map_zero' := by rw [map_zero, zero_mul, map_zero]
  map_add' a b := by
    rw [map_add, add_mul]
    exact (FiniteDeRhamP.uncompletedToFinite p m).map_add _ _

theorem finiteTerm_zero_of_le (m n : ℕ) (hmn : m ≤ n) (a : Logarithm.PeriodRings.AInf p) : finiteTerm p m n a = 0 := by
  change FiniteDeRhamP.uncompletedToFinite p m
    (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) a * ThetaDividedPowers.thetaDividedPower p n) = 0
  rw [map_mul, DenominatorBound.thetaDividedPower_finite_zero p m n hmn, mul_zero]

def finiteSeries (m : ℕ) : CoefficientCompletion p →+ FiniteDeRhamP.FiniteDeRham p m where
  toFun x := ∑ i ∈ Finset.range m, finiteTerm p m i (Coordinates.coordinate (p : Logarithm.PeriodRings.AInf p) i x)
  map_zero' := by simp only [map_zero, Finset.sum_const_zero]
  map_add' x y := by simp only [map_add, Finset.sum_add_distrib]

theorem finiteSeries_bound (m : ℕ) (x : CoefficientCompletion p) :
    ∃ r : ThetaQuotients.ThetaPowerQuotient p m,
      FiniteDeRhamP.integralToFinite p m r = (p : FiniteDeRhamP.FiniteDeRham p m) ^ m * finiteSeries p m x := by
  have h (i : ℕ) : ∃ r : ThetaQuotients.ThetaPowerQuotient p m,
      FiniteDeRhamP.integralToFinite p m r = (p : FiniteDeRhamP.FiniteDeRham p m) ^ m *
        finiteTerm p m i (Coordinates.coordinate (p : Logarithm.PeriodRings.AInf p) i x) :=
    DenominatorBound.uncompleted_denominator_bound p m _
  choose r hr using h
  refine ⟨∑ i ∈ Finset.range m, r i, ?_⟩
  simp only [map_sum, hr, Finset.mul_sum, finiteSeries, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

theorem finiteSeries_of_single (m n : ℕ) (a : Logarithm.PeriodRings.AInf p) :
    finiteSeries p m (AdicCompletion.of (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (ℕ →₀ Logarithm.PeriodRings.AInf p) (Finsupp.single n a)) =
      if n < m then finiteTerm p m n a else 0 := by
  classical
  change (∑ i ∈ Finset.range m, finiteTerm p m i
    (Coordinates.coordinate (p : Logarithm.PeriodRings.AInf p) i (AdicCompletion.of _ (ℕ →₀ Logarithm.PeriodRings.AInf p) (Finsupp.single n a)))) = _
  simp only [Coordinates.coordinate_of, Finsupp.single_apply, apply_ite, map_zero,
    Finset.sum_ite_eq, Finset.mem_range]
  split_ifs <;> rfl

def actualFinite (m : ℕ) : CoefficientCompletion p →+ FiniteDeRhamP.FiniteDeRham p m :=
  (Comparison.aCrisToFinite p m).toAddMonoidHom.comp (DividedPowerCompletion.completedDividedPowers p).toAddMonoidHom

theorem actualFinite_of_single (m n : ℕ) (a : Logarithm.PeriodRings.AInf p) :
    actualFinite p m (AdicCompletion.of (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (ℕ →₀ Logarithm.PeriodRings.AInf p) (Finsupp.single n a)) =
      finiteTerm p m n a := by
  change Comparison.aCrisToFinite p m (DividedPowerCompletion.completedDividedPowers p
    (AdicCompletion.of (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (ℕ →₀ Logarithm.PeriodRings.AInf p) (Finsupp.single n a))) = _
  rw [DividedPowerCompletion.completedDividedPowers_of, Comparison.aCrisToFinite_of]
  change FiniteDeRhamP.uncompletedToFinite p m (Finsupp.linearCombination (Logarithm.PeriodRings.AInf p) (ThetaDividedPowers.thetaDividedPower p) (Finsupp.single n a)) = _
  rw [Finsupp.linearCombination_single]
  rw [Algebra.smul_def]
  rfl

theorem actualFinite_dense (m : ℕ) (f : ℕ →₀ Logarithm.PeriodRings.AInf p) :
    actualFinite p m (AdicCompletion.of (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (ℕ →₀ Logarithm.PeriodRings.AInf p) f) =
      finiteSeries p m (AdicCompletion.of (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (ℕ →₀ Logarithm.PeriodRings.AInf p) f) := by
  have he : (actualFinite p m).comp (AdicCompletion.of (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (ℕ →₀ Logarithm.PeriodRings.AInf p)).toAddMonoidHom =
      (finiteSeries p m).comp (AdicCompletion.of (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (ℕ →₀ Logarithm.PeriodRings.AInf p)).toAddMonoidHom := by
    apply Finsupp.addHom_ext
    intro n a
    change actualFinite p m (AdicCompletion.of _ (ℕ →₀ Logarithm.PeriodRings.AInf p) (Finsupp.single n a)) =
      finiteSeries p m (AdicCompletion.of _ (ℕ →₀ Logarithm.PeriodRings.AInf p) (Finsupp.single n a))
    rw [actualFinite_of_single, finiteSeries_of_single]
    split_ifs with hn
    · rfl
    · exact finiteTerm_zero_of_le p m n (Nat.le_of_not_gt hn) a
  exact DFunLike.congr_fun he f

theorem actualFinite_eq_series (m : ℕ) : actualFinite p m = finiteSeries p m :=
  BoundedCompletion.ModuleComparison.bounded_addHom_unique p (FiniteDeRhamP.integralToFinite p m) (FiniteDeRhamP.integralToFinite_injective p m) m (FiniteDeRhamP.p_isUnit p m)
    (actualFinite p m) (finiteSeries p m) (actualFinite_dense p m)
    (fun x => Comparison.aCrisToFinite_bound p m (DividedPowerCompletion.completedDividedPowers p x)) (finiteSeries_bound p m)

theorem finite_comparison_series (m : ℕ) (x : CoefficientCompletion p) :
    Comparison.aCrisToFinite p m (DividedPowerCompletion.completedDividedPowers p x) =
      ∑ i ∈ Finset.range m, finiteTerm p m i (Coordinates.coordinate (p : Logarithm.PeriodRings.AInf p) i x) :=
  DFunLike.congr_fun (actualFinite_eq_series p m) x

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteSeriesComparison
