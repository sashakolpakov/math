import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

/-! # Character Range -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CharacterRange.GeneralizedHecke

noncomputable section

/-! A character factoring through a finite-dimensional linear realization has finite rational image. -/

variable {K V W Z : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup Z] [Module K Z] [FiniteDimensional K W]

theorem finite_range_of_ker_le (f : V →ₗ[K] W) (g : V →ₗ[K] Z)
    (hker : f.ker ≤ g.ker) : FiniteDimensional K g.range := by
  let : FiniteDimensional K (V ⧸ f.ker) := Module.Finite.of_injective
    f.quotKerEquivRange.toLinearMap f.quotKerEquivRange.injective
  have hfinite : FiniteDimensional K (f.ker.liftQ g hker).range := Module.Finite.range _
  rw [Submodule.range_liftQ] at hfinite
  exact hfinite

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CharacterRange.GeneralizedHecke
