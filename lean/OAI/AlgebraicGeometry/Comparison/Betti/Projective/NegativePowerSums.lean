import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ModuleClosure

/-! # Negative Power Sums -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativePowerSums.Dolbeault

noncomputable section

/-! The actual comparison and intersection acyclicity hold for the finite sums used by projective resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveNegativePower_eq_twist (n : ℕ) (j : Fin (n + 1)) (k : ℕ) :
    SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := ℂ) j k = SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j (-(k : ℤ)) := by
  cases k <;> rfl

theorem projectiveAnalyticCechAcyclic_negativePower (n : ℕ) (j : Fin (n + 1)) (k : ℕ) :
    ModuleCechAcyclicity.Dolbeault.projectiveAnalyticCechAcyclic n (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := ℂ) j k) := by
  rw [projectiveNegativePower_eq_twist]
  exact ModuleCechAcyclicity.Dolbeault.projectiveAnalyticCechAcyclic_twist n j (-(k : ℤ))

theorem projectiveModuleComparisonIsomorphism_negativePower (n : ℕ) (j : Fin (n + 2)) (k : ℕ) :
    ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism (n + 1) (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := ℂ) j k) := by
  rw [projectiveNegativePower_eq_twist]
  exact ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism_twist n j (-(k : ℤ))

theorem projectiveAnalyticCechAcyclic_negativePowerSum (n : ℕ) (j : Fin (n + 1))
    {ι : Type} [Fintype ι] (k : ι → ℕ) :
    ModuleCechAcyclicity.Dolbeault.projectiveAnalyticCechAcyclic n (∐ fun i => SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := ℂ) j (k i)) :=
  ModuleCechAcyclicity.Dolbeault.projectiveAnalyticCechAcyclic_finiteCoproduct n _ (fun i => projectiveAnalyticCechAcyclic_negativePower n j (k i))

theorem projectiveModuleComparisonIsomorphism_negativePowerSum (n : ℕ) (j : Fin (n + 2))
    {ι : Type} [Fintype ι] (k : ι → ℕ) :
    ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism (n + 1) (∐ fun i => SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := ℂ) j (k i)) :=
  ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism_finiteCoproduct (n + 1) _
    (fun i => projectiveModuleComparisonIsomorphism_negativePower n j (k i))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativePowerSums.Dolbeault
