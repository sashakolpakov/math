import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteEtaleDualBasis

/-! # Trace Dual Base Change -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.TraceDualBaseChange

noncomputable section

/-! # The actual trace-dual basis commutes with extension of the coefficient ring -/

open scoped TensorProduct

universe u v
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [Module.Free A B] [Module.Finite A B] [Algebra.Etale A B]
  {ι : Type v} [Fintype ι] (b : Module.Basis ι A B)
  (F : Type u) [CommRing F] [Algebra A F]

theorem dual (i : ι) : FiniteEtaleDualBasis.dualBasis (b.baseChange F) i =
    1 ⊗ₜ[A] FiniteEtaleDualBasis.dualBasis b i := by
  classical
  apply (FiniteEtaleDualBasis.bijective (b.baseChange F)).injective
  apply (b.baseChange F).equivFun.injective
  funext j
  rw [TracePairingBasis.coordinate, TracePairingBasis.coordinate,
    FiniteEtaleDualBasis.trace_basis_dual, Module.Basis.baseChange_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, AlgebraTraceBaseChange.includeRight,
    FiniteEtaleDualBasis.trace_basis_dual]
  split_ifs <;> simp only [map_one, map_zero]

theorem expansion (x : F ⊗[A] B) :
    (∑ i, Algebra.trace F (F ⊗[A] B) ((1 ⊗ₜ[A] FiniteEtaleDualBasis.dualBasis b i) * x) •
      (1 ⊗ₜ[A] b i)) = x := by
  simpa only [dual, Module.Basis.baseChange_apply] using
    FiniteEtaleDualBasis.expansion (b.baseChange F) x

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.TraceDualBaseChange
