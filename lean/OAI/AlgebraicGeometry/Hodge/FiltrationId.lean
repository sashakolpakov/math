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
import OAI.AlgebraicGeometry.Hodge.Filtration
import OAI.CategoryTheory.ConcreteCategory.Notation

/-! # Filtration Id -/

namespace OAI.AlgebraicGeometry

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

open _root_.AlgebraicGeometry

/-!
# The Hodge filtration

Lemmas about the definitions in
`OAI.AlgebraicGeometry.Hodge.Filtration`.
-/

/-! ### Constructions used only in proofs -/

section

open _root_.CategoryTheory Limits _root_.TopologicalSpace
open scoped TensorProduct

open OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ))

attribute [local instance] ComplexPoint.Basic.ComplexSchemePoint.analyticHasDerivedCategory

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf

/-- A rational number as a morphism from the integer to the rational constant sheaf. -/
def ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf (q : K) :
    𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℤ) ⟶ 𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); K) :=
  (AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(ComplexPoint.Basic.ComplexSchemePoint X)).map
    (AddCommGrpCat.ofHom (zmultiplesAddHom K q))

omit [Algebra K ℂ] in
@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf_zero :
    ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf K X 0 = 0 := by
  unfold ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf
  rw [map_zero (zmultiplesAddHom K)]
  have h : AddCommGrpCat.ofHom (0 : ℤ →+ K) = 0 := AddCommGrpCat.hom_ext rfl
  rw [h, Functor.map_zero]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf_add (a b : K) :
    ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf K X (a + b) =
      ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf K X a +
        ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf K X b := by
  unfold ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf
  rw [map_add (zmultiplesAddHom K)]
  have h : AddCommGrpCat.ofHom
      (zmultiplesAddHom K a + zmultiplesAddHom K b) =
      AddCommGrpCat.ofHom (zmultiplesAddHom K a) +
        AddCommGrpCat.ofHom (zmultiplesAddHom K b) :=
    AddCommGrpCat.hom_ext rfl
  rw [h, Functor.map_add]
  rfl

/-- The source object of Mathlib's sheaf cohomology mapped to the constant integer sheaf. -/
def ComplexPoint.Basic.ComplexSchemePoint.uliftIntegerToIntegerConstantSheaf :
    (constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ 𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℤ) :=
  (AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(ComplexPoint.Basic.ComplexSchemePoint X)).map
    (AddCommGrpCat.ofHom (AddEquiv.ulift (α := ℤ)).toAddMonoidHom)

/-- The constant rational class `q` in degree-zero rational cohomology. -/
def ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass (q : K) : H^0(X; K) :=
  Abelian.Ext.mk₀ (ComplexPoint.Basic.ComplexSchemePoint.uliftIntegerToIntegerConstantSheaf X ≫ ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf K X q)

omit [Algebra K ℂ] in
@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass_zero :
    ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass K X 0 = 0 := by
  rw [ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass, ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf_zero]
  exact (congrArg Abelian.Ext.mk₀
    (Limits.comp_zero (f := ComplexPoint.Basic.ComplexSchemePoint.uliftIntegerToIntegerConstantSheaf X))).trans
    (Abelian.Ext.mk₀_zero _ _)

omit [Algebra K ℂ] in
@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass_add (a b : K) :
    ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass K X (a + b) =
      ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass K X a + ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass K X b := by
  rw [ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass, ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass, ComplexPoint.Basic.ComplexSchemePoint.fieldCohomologyClass,
    ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf_add]
  exact (congrArg Abelian.Ext.mk₀ (Preadditive.comp_add _ _ _ (ComplexPoint.Basic.ComplexSchemePoint.uliftIntegerToIntegerConstantSheaf X)
    (ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf K X a) (ComplexPoint.Basic.ComplexSchemePoint.integerToFieldConstantSheaf K X b))).trans
    (Abelian.Ext.mk₀_add _ _)

end

open _root_.CategoryTheory Limits _root_.TopologicalSpace
open scoped TensorProduct

open OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ))

attribute [local instance] ComplexPoint.Basic.ComplexSchemePoint.analyticHasDerivedCategory

omit [Algebra K ℂ] in
@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf_zero : ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf K X 0 = 0 := by
  unfold ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf
  rw [OAI.Algebra.Ring.Basic.AddMonoidHom.mulLeft_zero]
  have h : AddCommGrpCat.ofHom (0 : K →+ K) = 0 := AddCommGrpCat.hom_ext rfl
  rw [h, Functor.map_zero]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex_zero : ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex K X 0 = 0 := by
  unfold ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex
  rw [ComplexPoint.Basic.ComplexSchemePoint.fieldScalarSheaf_zero, Functor.map_zero, HomologicalComplex.extendMap_zero]

/-- Postcomposition by the zero map of complexes is the zero map on hypercohomology. -/
@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_zero
    {K L : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ} (n : ℤ) :
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (0 : K ⟶ L) n = 0 := by
  refine AddMonoidHom.ext fun α ↦ ?_
  apply (Localization.SmallShiftedHom.equiv
    (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  unfold ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap
  simp [Localization.SmallShiftedHom.equiv_comp,
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyEquiv_zero]

/-- Postcomposition by the identity map of complexes is the identity on hypercohomology. -/
@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_id
    {K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ} (n : ℤ) :
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (𝟙 K) n = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun α ↦ ?_
  let eK : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X K n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj K) n :=
    Localization.SmallShiftedHom.equiv
      (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q
  change α.comp
      (Localization.SmallShiftedHom.mk₀
        (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) 0 rfl (𝟙 K))
      (zero_add n) = α
  apply eK.injective
  simp [eK]

@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.deRhamConjSemilinear_apply [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : ComplexPoint.Basic.ComplexSchemePoint.DeRhamHypercohomology X n) :
    ComplexPoint.Basic.ComplexSchemePoint.deRhamConjSemilinear X n α = ComplexPoint.Basic.ComplexSchemePoint.deRhamConj X n α := rfl

/-! #### Real coefficient fields

The hypothesis `hK` below says conjugation fixes the image of `K` in `ℂ`, equivalently that
`K → ℂ` lands in `ℝ`. It holds for `ℚ` and fails for `ℚ(i) ⊆ ℂ`. -/

end

end OAI.AlgebraicGeometry
