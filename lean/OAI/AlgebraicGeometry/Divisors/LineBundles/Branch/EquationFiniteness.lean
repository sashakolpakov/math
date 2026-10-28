import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.EquationEuler

/-! # Equation Finiteness -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.EquationFiniteness.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite one-equation lengths from the actual branch annihilator

Finiteness is derived from a unit or from the constructed proper
annihilating parameter pair, before invoking the Euler coefficient formula.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [IsDomain R] [IsLocalRing R] [Module.Finite R M]

theorem branchEquation_lengths_finite (r x : R) (hr : r ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R)
    (hP : P ∈ (Ideal.span {r}).minimalPrimes)
    (hAnn : (Module.annihilator R M).radical = P) (hxP : x ∉ P) :
    Module.length R (MultiplicationSequence.BundleCycles.equationKernel x M) ≠ ⊤ ∧ Module.length R (MultiplicationSequence.BundleCycles.equationCokernel x M) ≠ ⊤ := by
  by_cases hu : IsUnit x
  · rw [EquationUnitLength.BundleCycles.equationKernel_length_zero_of_unit x hu, EquationUnitLength.BundleCycles.equationCokernel_length_zero_of_unit x hu]
    exact ⟨ENat.zero_ne_top, ENat.zero_ne_top⟩
  obtain ⟨y, hyI, _, hxy⟩ := AuxiliaryParameter.BundleCycles.branchIdeal_exists_proper_parameter r x hr hdim P
    (Module.annihilator R M) hP hAnn hxP hu
  have hyM : Module.IsTorsionBy R M y := fun {m} => Module.mem_annihilator.mp hyI m
  exact ⟨EquationFiniteLength.BundleCycles.equationKernel_finite_of_two_equations x y (LocalIntersectionFiniteness.BundleCycles.finiteLength_quotient_of_radical_maximal _ hxy) hyM,
    EquationFiniteLength.BundleCycles.equationCokernel_finite_of_two_equations x y (LocalIntersectionFiniteness.BundleCycles.finiteLength_quotient_of_radical_maximal _ hxy) hyM⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.EquationFiniteness.BundleCycles
