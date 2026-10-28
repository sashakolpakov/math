import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.EvaluationRelations
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlacePositions

/-! # Product Relations -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ProductRelations.CM

noncomputable section

/-! Pointwise zero relations among restricted pure functions are
preserved by the actual local linear operators fixing almost all vacua. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation.AdelicLocalConstancy

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlacePositions.CM

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
  {J : Type*} [Fintype J]

theorem relation_preserved
    (T : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N →ₗ[ℂ]
      RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hT : ∀ᶠ v in cofinite, T v (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)
    (c : J → ℂ) (f : J → ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ j, ∀ᶠ v in cofinite, f j v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)
    (h : ∀ x : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F,
      ∑ j, c j * ∏ᶠ v, (f j v).val (fun i => x i v) = 0)
    (y : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    ∑ j, c j * ∏ᶠ v, (T v (f j v)).val (fun i => y i v) = 0 := by
  have hgood : ∀ᶠ v in cofinite,
      (∀ j, f j v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) ∧ T v (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v :=
    (eventually_all.mpr hf).and hT
  have hbad : {v | ¬ ((∀ j, f j v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) ∧
      T v (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)}.Finite := hgood
  let S := hbad.toFinset
  have hs (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (hv : v ∉ S) :
      (∀ j, f j v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) ∧ T v (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v := by
    simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hv
  have hf' (j : J) : ∀ᶠ v in cofinite, T v (f j v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v := by
    filter_upwards [hf j, hT] with v hv ht
    rw [hv, ht]
  have hsf (j : J) (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (hv : v ∉ S) : f j v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v :=
    (hs v hv).1 j
  have hst (j : J) (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) (hv : v ∉ S) : T v (f j v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v := by
    rw [hsf j v hv]
    exact (hs v hv).2
  have hlocal (x : (v : S) → Fin N → v.val.adicCompletion F) :
      ∑ j, c j * ∏ v : S, (f j v.val).val (x v) = 0 := by
    have hx := h (PlacePositions.CM.extend F N S x)
    simpa only [PlacePositions.CM.pure_product_extension F N S _ (hf _) (hsf _)] using hx
  let e (v : S) : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.val.adicCompletion F) N →ₗ[ℂ]
      ((Fin N → v.val.adicCompletion F) → ℂ) := (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.val.adicCompletion F) N).subtype
  let l (v : S) : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.val.adicCompletion F) N →ₗ[ℂ] ℂ :=
    (LinearMap.proj (fun i => y i v.val)).comp ((e v).comp (T v.val))
  have hr := EvaluationRelations.CM.FunctionFamily.relation_functionals e (fun _ => Subtype.val_injective)
    c (fun j v => f j v.val) hlocal l
  change (∑ j, c j * ∏ v : S, (T v.val (f j v.val)).val (fun i => y i v.val)) = 0 at hr
  let tail := LocallyConstant.charFn ℂ (RepresentationTheory.Theta.Adelic.Evaluation.AdelicLocalConstancy.integralOutside_clopen F N S) y
  have hdec (j : J) : (∏ᶠ v, (T v (f j v)).val (fun i => y i v)) =
      tail * ∏ v : S, (T v.val (f j v.val)).val (fun i => y i v.val) := by
    rw [RepresentationTheory.Theta.Adelic.Evaluation.AdelicLocalConstancy.pure_product_decomposition F N _ (hf' j) S (hst j), ← Finset.prod_coe_sort S]
  calc
    _ = tail * (∑ j, c j * ∏ v : S, (T v.val (f j v.val)).val (fun i => y i v.val)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hdec]
      ring
    _ = 0 := by rw [hr, mul_zero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ProductRelations.CM
