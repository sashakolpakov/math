import OAI.NumberTheory.PadicHodge.PeriodInvariants.AlgebraTraceBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Trace Pairing Basis -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.TracePairingBasis

noncomputable section

/-! # A basis realizes the trace pairing as an endomorphism compatible with base change -/

open scoped TensorProduct

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι]
  (b : Module.Basis ι R S)

def linear : S →ₗ[R] S :=
  b.equivFun.symm.toLinearMap.comp (LinearMap.pi (fun i => Algebra.traceForm R S (b i)))

theorem coordinate (x : S) (i : ι) :
    b.equivFun (linear b x) i = Algebra.trace R S (b i * x) := by
  change b.equivFun (b.equivFun.symm (fun i => Algebra.traceForm R S (b i) x)) i = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem linear_apply (x : S) : linear b x = ∑ i, Algebra.trace R S (b i * x) • b i :=
  b.equivFun_symm_apply (fun i => Algebra.trace R S (b i * x))

theorem injective (h : (Algebra.traceForm R S).Nondegenerate) : Function.Injective (linear b) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hc : ∀ i, Algebra.traceForm R S (b i) x = 0 := by
    intro i
    have he := congrArg (fun y => b.equivFun y i) hx
    rw [coordinate, map_zero, Pi.zero_apply] at he
    exact he
  apply h.2 x
  intro y
  rw [← b.sum_repr y, map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul, LinearMap.smul_apply, hc, smul_zero]

variable [Module.Free R S] [Module.Finite R S]
  (T : Type*) [CommRing T] [Algebra R T]

theorem baseChange : (linear b).baseChange T = linear (b.baseChange T) := by
  apply (b.baseChange T).ext
  intro i
  rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul, linear_apply, linear_apply]
  rw [TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Module.Basis.baseChange_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    AlgebraTraceBaseChange.includeRight]
  rw [TensorProduct.tmul_smul, IsScalarTower.algebraMap_smul]

theorem surjective {K E κ : Type*} [Field K] [CommRing E] [Algebra K E]
    [FiniteDimensional K E] [Fintype κ] (c : Module.Basis κ K E)
    (h : (Algebra.traceForm K E).Nondegenerate) : Function.Surjective (linear c) :=
  LinearMap.injective_iff_surjective.mp (injective c h)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.TracePairingBasis
