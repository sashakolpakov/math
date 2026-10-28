/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Hodge.AnalyticDifferentialForms

/-! # Analytic Differential Lt -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Analytic differential forms

-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

attribute [local instance] ComplexPoint.Basic.ComplexSchemePoint.chartFieldModule

attribute [local instance] ComplexPoint.Basic.ComplexSchemePoint.chartFieldTower

lemma ComplexPoint.Basic.ComplexSchemePoint.formRestriction_differential [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (θ : Algebra.DeRham.Basic.Form ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p) :
    ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d i (p + 1)
        (Algebra.DeRham.Basic.differential ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p θ) =
      Algebra.DeRham.Basic.differential ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d V) p
        (ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d i p θ) :=
  Algebra.DeRham.BasicSquared.map_differential ℂ (ComplexPoint.Basic.ComplexSchemePoint.holomorphicRestrictionAlgHom X d i) p θ

lemma ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel_eq_top_of_lt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    {p : ℕ} (hp : d < p) : ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U p = ⊤ := by
  refine top_unique fun θ _ ↦ ?_
  refine (ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_iff X d U p θ).2 fun z y hy ↦
    ContinuousAlternatingMap.ext fun v ↦ ?_
  refine (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X d U z p θ y).toAlternatingMap.map_linearDependent _ fun hli ↦ ?_
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hcard
  lia

lemma ComplexPoint.Basic.ComplexSchemePoint.holomorphicForm_eq_zero_of_lt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    {p : ℕ} (hp : d < p) (θ : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d U p) : θ = 0 := by
  obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U p) θ
  change Submodule.Quotient.mk θ = 0
  rw [Submodule.Quotient.mk_eq_zero, ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel_eq_top_of_lt X d U hp]
  trivial

lemma ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential_squared [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) (p : ℕ)
    (θ : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d U p) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X d U (p + 1)
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X d U p θ) = 0 := by
  obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U p) θ
  change Submodule.Quotient.mk
    (Algebra.DeRham.Basic.differential ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (p + 1)
      (Algebra.DeRham.Basic.differential ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p θ)) = 0
  rw [Algebra.DeRham.BasicSquared.differential_squared]
  exact Submodule.Quotient.mk_zero _

lemma ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction_differential [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (θ : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d U p) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d i (p + 1)
        (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X d U p θ) =
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X d V p
        (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d i p θ) := by
  obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U p) θ
  change Submodule.Quotient.mk
      (ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d i (p + 1)
        (Algebra.DeRham.Basic.differential ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) p θ)) =
    Submodule.Quotient.mk
      (Algebra.DeRham.Basic.differential ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d V) p
        (ComplexPoint.Basic.ComplexSchemePoint.formRestriction X d i p θ))
  rw [ComplexPoint.Basic.ComplexSchemePoint.formRestriction_differential]

end

end OAI.AlgebraicGeometry
