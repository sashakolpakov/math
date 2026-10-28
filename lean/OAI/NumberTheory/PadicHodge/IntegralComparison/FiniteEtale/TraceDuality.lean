import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleDualBasis

/-! # Trace Duality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceDuality

noncomputable section

/-! The finite free étale trace identifies the algebra with its actual
linear dual. Evaluation at one is the coefficient trace. -/

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Free A B] [Module.Finite A B] [Algebra.Etale A B]

theorem bijective : Function.Bijective (Algebra.traceForm A B) := by
  classical
  let b := Module.Free.chooseBasis A B
  constructor
  · intro x y h
    apply (PeriodInvariants.FiniteEtaleDualBasis.bijective b).injective
    apply b.equivFun.injective
    funext i
    rw [PeriodInvariants.TracePairingBasis.coordinate, PeriodInvariants.TracePairingBasis.coordinate]
    simpa only [Algebra.traceForm_apply, mul_comm] using LinearMap.congr_fun h (b i)
  · intro φ
    refine ⟨∑ i, φ (b i) • PeriodInvariants.FiniteEtaleDualBasis.dualBasis b i, ?_⟩
    apply b.ext
    intro j
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      Algebra.traceForm_apply, PeriodInvariants.FiniteEtaleDualBasis.trace_dual_basis,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]

def equiv : B ≃ₗ[A] Module.Dual A B :=
  LinearEquiv.ofBijective (Algebra.traceForm A B) (bijective A B)

theorem equiv_apply (x y : B) : equiv A B x y = Algebra.trace A B (x * y) := rfl

theorem equiv_apply_one (x : B) : equiv A B x 1 = Algebra.trace A B x := by
  rw [equiv_apply, mul_one]

theorem equiv_mul (x y z : B) : equiv A B (x * y) z = equiv A B y (x * z) := by
  simp only [equiv_apply]
  rw [mul_assoc, mul_left_comm]

theorem trace_eq_eval_one (φ : Module.Dual A B) :
    Algebra.trace A B ((equiv A B).symm φ) = φ 1 := by
  rw [← equiv_apply_one, LinearEquiv.apply_symm_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceDuality
