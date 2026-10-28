import OAI.RepresentationTheory.Theta.Adelic.Evaluation

/-! # Place Positions -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlacePositions.CM

noncomputable section

/-! Extend arbitrary positions at finitely many places by zero, in the
actual finite adele ring, and evaluate restricted pure tensors there. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation.AdelicLocalConstancy

variable (F : Type) [Field F] [NumberField F] (N : ℕ) (S : Finset (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F))

def extend (x : (v : S) → Fin N → v.val.adicCompletion F) : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F :=
  fun i => ⟨fun v => if hv : v ∈ S then x ⟨v, hv⟩ i else 0, by
    filter_upwards [show ∀ᶠ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F in cofinite, v ∉ S from by simp] with v hv
    simp only [dite_eq_right hv]
    exact (v.adicCompletionIntegers F).zero_mem⟩

theorem extend_inside (x : (v : S) → Fin N → v.val.adicCompletion F) (v : S) (i : Fin N) :
    extend F N S x i v.val = x v i := by
  change (if hv : v.val ∈ S then x ⟨v.val, hv⟩ i else 0) = x v i
  rw [dite_eq_left v.property]

theorem extend_outside (x : (v : S) → Fin N → v.val.adicCompletion F)
    (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (hv : v ∉ S) (i : Fin N) : extend F N S x i v = 0 :=
  dite_eq_right hv

theorem extend_integral (x : (v : S) → Fin N → v.val.adicCompletion F) :
    extend F N S x ∈ RepresentationTheory.Theta.Adelic.Evaluation.AdelicLocalConstancy.integralOutside F N S := by
  intro v hv i
  rw [extend_outside F N S x v hv i]
  exact (v.adicCompletionIntegers F).zero_mem

theorem pure_product_extension
    (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)
    (hs : ∀ v, v ∉ S → f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)
    (x : (v : S) → Fin N → v.val.adicCompletion F) :
    (∏ᶠ v, (f v).val (fun i => extend F N S x i v)) = ∏ v : S, (f v.val).val (x v) := by
  rw [RepresentationTheory.Theta.Adelic.Evaluation.AdelicLocalConstancy.pure_product_decomposition F N f hf S hs,
    (LocallyConstant.charFn_eq_one ℂ _ _).mpr (extend_integral F N S x), one_mul,
    ← Finset.prod_coe_sort S]
  apply Finset.prod_congr rfl
  intro v _
  exact congrArg (f v.val).val (funext (extend_inside F N S x v))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlacePositions.CM
