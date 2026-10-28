import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodCoefficients
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Singular Coefficient Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientLift

noncomputable section

/-! Lift actual singular degree-one classes through surjections from
divisible coefficients on a torus with a free lattice. -/

open _root_.CategoryTheory

theorem free_character_lift {L A B : Type} [AddCommGroup L] [AddCommGroup A]
    [AddCommGroup B] [Module.Free ℤ L]
    (f : A →+ B) (hf : Function.Surjective f) (c : L →+ B) :
    ∃ b : L →+ A, f.comp b = c := by
  let e := Module.Free.chooseBasis ℤ L
  let b := e.constr ℤ (fun i => (hf (c (e i))).choose)
  have h : f.toIntLinearMap.comp b = c.toIntLinearMap := by
    apply e.ext
    intro i
    change f (b (e i)) = c (e i)
    rw [e.constr_basis]
    exact (hf (c (e i))).choose_spec
  exact ⟨b.toAddMonoidHom, congrArg LinearMap.toAddMonoidHom h⟩

variable {R : Type} [Ring R] {M N : ModuleCat.{0} R}
  (f : M ⟶ N) (hf : Function.Surjective f) [DivisibleBy M ℤ]
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Λ : Submodule ℤ V) [DiscreteTopology Λ] [Module.Free ℤ Λ]

include hf in
theorem singularH1_coefficient_surjective : Function.Surjective (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap f (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) := by
  intro a
  obtain ⟨b, hb⟩ := free_character_lift f.hom.toAddMonoidHom hf
    (Integral.SingularPeriods.IntegralSingularPeriods.cohomologyPeriod N Λ a)
  obtain ⟨c, hc⟩ := SingularPeriodCoefficients.DivisibleSingularPeriods.cohomologyPeriod_surjective M Λ b
  refine ⟨c, Integral.SingularPeriods.IntegralSingularPeriods.cohomologyPeriod_injective N Λ ?_⟩
  rw [SingularPeriodCoefficients.IntegralSingularPeriods.cohomologyPeriod_coefficient, hc]
  exact hb

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientLift
