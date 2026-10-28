import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolevAdjoints

/-! # Strong Cutoff Operators -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffOperators.CM.Construction

noncomputable section

/-! Scalar cutoff multiplication and its actual real Hilbert adjoint preserve
every Sobolev order. The adjoint is multiplication by the conjugate cutoff. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ComplexConjugate

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

def schwartzConjugate (g : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap g

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem schwartzConjugate_apply (g : 𝓢(E, ℂ)) (x : E) :
    schwartzConjugate g x = starRingEnd ℂ (g x) := rfl

theorem strongSobolev_schwartz_multiply (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (g : 𝓢(E, ℂ)) (u : Lp ℂ 2 (volume : Measure E))
    (hu : StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u) :
    StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (CutoffDifferential.CM.Construction.schwartzL2Multiply g u) := by
  apply (StrongSobolev.CM.Construction.strongSobolev_iff_memSobolev b n _).mpr
  rw [CutoffDifferential.CM.Construction.schwartzL2Multiply_distribution]
  exact SobolevInv.CM.Construction.memSobolev_nat_schwartz_cutoff n g ((StrongSobolev.CM.Construction.strongSobolev_iff_memSobolev b n u).mp hu)

omit [Fintype ι] in
theorem schwartzL2Multiply_real_adjoint (g : 𝓢(E, ℂ)) :
    ((CutoffDifferential.CM.Construction.schwartzL2Multiply (F := ℂ) g).restrictScalars ℝ).adjoint =
      (CutoffDifferential.CM.Construction.schwartzL2Multiply (F := ℂ) (schwartzConjugate g)).restrictScalars ℝ := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  change (∫ x, inner ℝ (u x) (CutoffDifferential.CM.Construction.schwartzL2Multiply g v x)) =
    ∫ x, inner ℝ (CutoffDifferential.CM.Construction.schwartzL2Multiply (schwartzConjugate g) u x) (v x)
  apply integral_congr_ae
  filter_upwards [CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g v, CutoffDifferential.CM.Construction.schwartzL2Multiply_coe (schwartzConjugate g) u]
    with x hv hu
  rw [hv, hu, schwartzConjugate_apply]
  simp only [smul_eq_mul, Complex.inner, map_mul, starRingEnd_self_apply]
  congr 1
  ring

theorem strongSobolev_schwartz_multiply_adjoint (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (g : 𝓢(E, ℂ)) (u : Lp ℂ 2 (volume : Measure E))
    (hu : StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u) :
    StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (((CutoffDifferential.CM.Construction.schwartzL2Multiply (F := ℂ) g).restrictScalars ℝ).adjoint u) := by
  rw [schwartzL2Multiply_real_adjoint]
  exact strongSobolev_schwartz_multiply b n (schwartzConjugate g) u hu

theorem strongSobolev_finset_sum {F J : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (b : OrthonormalBasis ι ℝ E) (n : ℕ) (s : Finset J) (u : J → Lp F 2 (volume : Measure E))
    (hu : ∀ j ∈ s, StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (u j)) :
    StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (∑ j ∈ s, u j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using StrongSobolev.CM.Construction.strongSobolev_zero (F := F) b n
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hu j (Finset.mem_insert_self j s)).add b n
      (ih (fun k hk => hu k (Finset.mem_insert_of_mem hk)))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffOperators.CM.Construction
