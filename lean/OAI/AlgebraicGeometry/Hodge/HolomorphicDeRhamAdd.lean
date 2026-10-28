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
import OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham
import OAI.AlgebraicGeometry.Hodge.HolomorphicPoincare
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Topology.Sheaves.Sheafify
import OAI.Topology.Sheaves.StalkExact
import OAI.AlgebraicGeometry.Hodge.AnalyticDifferentialLt
import OAI.AlgebraicGeometry.Smooth.Equidimensional
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Topology.Sheaves.Abelian
import OAI.CategoryTheory.ConcreteCategory.Notation

/-! # Holomorphic De Rham Add -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# The holomorphic de Rham complex

-/

/-! ### Constructions used only in proofs -/

section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold
variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- Multiplication by a complex scalar on the presheaf of holomorphic de Rham forms. -/
def ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf [SmoothOfRelativeDimension d X.hom]
    (p : ℕ) (c : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d p ⟶
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d p where
  app U := AddCommGrpCat.ofHom
    ((c • LinearMap.id : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d U p →ₗ[ℂ] _).toAddMonoidHom)
  naturality {U V} i := by
    ext x
    dsimp [ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf] at x ⊢
    change c • ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d i p x =
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d i p (c • x)
    exact (LinearMap.map_smul _ c x).symm

/-- Scalar multiplication commutes with the exterior derivative. -/
lemma ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_d
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (c : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p c ≫
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d p =
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d p ≫
      ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d (p + 1) c :=
  NatTrans.ext <| funext fun U => AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun x =>
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X d U p).map_smul c x

/-- Multiplication by a complex scalar as an endomorphism of the sheafified de Rham complex. -/
def ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex [SmoothOfRelativeDimension d X.hom]
    (c : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X d ⟶
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X d :=
  CochainComplex.ofHom
    (fun p =>
      let J := Opens.grothendieckTopology
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      (presheafToSheaf J AddCommGrpCat).map
        (ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p c))
    (fun p => by
      let J := Opens.grothendieckTopology
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      unfold ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex
      simp only [CochainComplex.of_d]
      change (presheafToSheaf J AddCommGrpCat).map
          (ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p c) ≫
        (presheafToSheaf J AddCommGrpCat).map
          (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d p) =
        (presheafToSheaf J AddCommGrpCat).map
          (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d p) ≫
        (presheafToSheaf J AddCommGrpCat).map
          (ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d (p + 1) c)
      rw [← Functor.map_comp, ← Functor.map_comp,
        ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_d])

/-- Multiplication by a complex scalar on the integer-indexed holomorphic de Rham complex. -/
def ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt [IsIntegral X.left] [Smooth X.hom]
    (c : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplexInt X ⟶
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplexInt X :=
  HomologicalComplex.extendMap
    (ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) c) ComplexShape.embeddingUpNat

end

section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- Scalar multiplication on the constant complex presheaf. -/
def ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf (c : ℂ) :
    𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ⟶ 𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) where
  app _ := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c)
  naturality {U V} i := by
    ext x
    rfl

/-- Scalar multiplication on the constant complex sheaf. -/
def ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf (c : ℂ) :
    𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ⟶ 𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) :=
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
  (presheafToSheaf J AddCommGrpCat).map
    (ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf X c)

/-- Scalar multiplication on the constant complex-valued complex concentrated in degree zero. -/
@[implicit_reducible]
def ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex (c : ℂ) :
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).obj
        𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ⟶
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).obj
        𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) :=
  (CochainComplex.single₀ _).map (ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf X c)

/-- Scalar multiplication on the integer-indexed constant complex-valued complex. -/
def ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt (c : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt X ⟶
      ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt X :=
  HomologicalComplex.extendMap (ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex X c)
    ComplexShape.embeddingUpNat

end

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_apply
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (c : ℂ)
    (U : (Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ)
    (x : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d U p) :
    (ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p c).app U x = c • x := rfl

@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_zero
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p 0 = 0 := by
  dsimp [ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf, ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf]
  simp
  rfl

@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_one
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p 1 = 𝟙 _ := by
  dsimp [ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf, ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf]
  simp
  rfl

@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_add
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (a b : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p (a + b) =
      ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p a +
        ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p b := by
  dsimp [ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf, ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf]
  simp [add_smul]
  rfl

@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_mul
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (a b : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p (a * b) =
      ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p b ≫
        ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p a := by
  dsimp [ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf, ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf]
  simp [mul_smul]
  rfl

@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_zero
    [SmoothOfRelativeDimension d X.hom] :
    ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d 0 = 0 := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
      AddCommGrpCat).map
      (ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p 0) = 0
  rw [ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_zero, Functor.map_zero]

@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_one
    [SmoothOfRelativeDimension d X.hom] :
    ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d 1 = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
      AddCommGrpCat).map
      (ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p 1) = 𝟙 _
  rw [ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_one]
  exact (presheafToSheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    AddCommGrpCat).map_id _

@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_add
    [SmoothOfRelativeDimension d X.hom] (a b : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d (a + b) =
      ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d a +
        ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d b := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
      AddCommGrpCat).map
      (ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p (a + b)) = _
  rw [ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_add, Functor.map_add]
  rfl

@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_mul
    [SmoothOfRelativeDimension d X.hom] (a b : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d (a * b) =
      ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d b ≫
        ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d a := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
      AddCommGrpCat).map
      (ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d p (a * b)) = _
  rw [ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf_mul, Functor.map_comp]
  rfl

/-- Conjugation intertwines multiplication by `c` with multiplication by `conj c` on the constant
complex presheaf. This is the presheaf-level source of conjugate-linearity. -/
lemma ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf_comp_conj (c : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf X c ≫ ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexPresheaf X =
      ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexPresheaf X ≫
        ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf X (starRingEnd ℂ c) := by
  ext U : 2
  exact AddMonoidHom.ext (map_mul (starRingEnd ℂ) c)

/-- Conjugation intertwines multiplication by `c` with multiplication by `conj c` on the constant
complex sheaf. -/
lemma ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf_comp_conj (c : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf X c ≫ ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexSheaf X =
      ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexSheaf X ≫
        ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf X (starRingEnd ℂ c) := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
  change (presheafToSheaf J AddCommGrpCat).map (ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf X c) ≫
      (presheafToSheaf J AddCommGrpCat).map (ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexPresheaf X) =
    (presheafToSheaf J AddCommGrpCat).map (ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexPresheaf X) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf X (starRingEnd ℂ c))
  rw [← Functor.map_comp, ← Functor.map_comp, ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf_comp_conj]

/-- The inclusion of constant zero-forms commutes with complex scalar multiplication. -/
lemma ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero_scalar
    [SmoothOfRelativeDimension d X.hom] (c : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf X d ≫
      (let J := Opens.grothendieckTopology
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      (presheafToSheaf J AddCommGrpCat).map
        (ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d 0 c)) =
    ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf X c ≫
      ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf X d := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
  change (presheafToSheaf J AddCommGrpCat).map
      (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamPresheaf X d 0 c) =
    (presheafToSheaf J AddCommGrpCat).map
      (ComplexPoint.Basic.ComplexSchemePoint.complexScalarPresheaf X c) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  let f := ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant X d U
  change (c • LinearMap.id).toAddMonoidHom.comp f.toAddMonoidHom =
    f.toAddMonoidHom.comp (DistribSMul.toAddMonoidHom ℂ c)
  ext x
  exact (f.map_smul c x).symm

/-- The constant-to-de Rham comparison commutes with complex scalar multiplication. -/
lemma ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex_scalar
    [SmoothOfRelativeDimension d X.hom] (c : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X d ≫
      ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X d c =
    ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex X c ≫
      ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X d := by
  apply HomologicalComplex.hom_ext
  intro p
  rcases p with _ | p
  · exact ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero_scalar X d c
  · apply (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℕ) 0 𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) (p + 1)
      (Nat.succ_ne_zero p)).eq_of_src

/-- Conjugation intertwines the two scalar multiplications in degree zero. -/
lemma ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex_comp_conj (c : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex X c ≫ ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexComplex X =
      ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexComplex X ≫
        ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex X (starRingEnd ℂ c) := by
  unfold ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexComplex
  rw [← Functor.map_comp, ← Functor.map_comp, ComplexPoint.Basic.ComplexSchemePoint.complexScalarSheaf_comp_conj]

/-- Conjugation intertwines multiplication by `c` with multiplication by `conj c` on the
integer-indexed constant complex. -/
lemma ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt_comp_conj (c : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X c ≫ ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexSheafComplexInt X =
      ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexSheafComplexInt X ≫
        ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X (starRingEnd ℂ c) := by
  unfold ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexSheafComplexInt
    ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex_comp_conj]

@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt_zero
    [IsIntegral X.left] [Smooth X.hom] :
    ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X 0 = 0 := by
  unfold ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt
  rw [ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_zero, HomologicalComplex.extendMap_zero]
  rfl

@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt_one
    [IsIntegral X.left] [Smooth X.hom] :
    ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X 1 = 𝟙 _ := by
  unfold ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplexInt
  rw [ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_one]
  exact HomologicalComplex.extendMap_id _ _

@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt_add
    [IsIntegral X.left] [Smooth X.hom] (a b : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X (a + b) =
      ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X a +
        ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X b := by
  unfold ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt
  rw [ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_add, HomologicalComplex.extendMap_add]
  rfl

@[simp] lemma ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt_mul
    [IsIntegral X.left] [Smooth X.hom] (a b : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X (a * b) =
      ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X b ≫
        ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X a := by
  unfold ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt
  rw [ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex_mul, HomologicalComplex.extendMap_comp]
  rfl

/-- The integer-indexed constant-to-de Rham comparison commutes with complex scalar
multiplication. -/
lemma ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt_scalar
    [IsIntegral X.left] [Smooth X.hom] (c : ℂ) :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X ≫
      ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplexInt X c =
    ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplexInt X c ≫
      ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X := by
  change HomologicalComplex.extendMap
      (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      (ComplexPoint.Basic.ComplexSchemePoint.scalarHolomorphicDeRhamComplex X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) c) ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
      (ComplexPoint.Basic.ComplexSchemePoint.complexScalarComplex X c) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)) ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex_scalar]

end

end OAI.AlgebraicGeometry
