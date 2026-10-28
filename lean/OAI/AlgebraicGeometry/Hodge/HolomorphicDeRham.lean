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
import OAI.AlgebraicTopology.Sheaf.Constant
import OAI.AlgebraicGeometry.Hodge.AnalyticDifferentialLt
import OAI.AlgebraicGeometry.Smooth.Equidimensional
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Topology.Sheaves.Abelian
import OAI.CategoryTheory.ConcreteCategory.Notation
import OAI.AlgebraicGeometry.Hodge.HolomorphicPoincare
import OAI.Topology.Sheaves.StalkExact
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Topology.Sheaves.Sheafify

/-! # Holomorphic De Rham -/

namespace OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

noncomputable section

open _root_.AlgebraicGeometry

/-!
# The holomorphic de Rham complex

This file assembles the analytic differential forms constructed from manifold derivatives
into a presheaf complex and then sheafifies it degree by degree. Restriction of functions induces
restriction of forms and commutes with the exterior derivative.

Constant complex-valued functions define a canonical morphism from the constant sheaf complex to
the holomorphic de Rham complex. Both complexes are also extended by zero to integer degrees for
use in the derived category.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. Holomorphic
forms are defined as Kähler forms of the algebra of holomorphic functions, modulo forms whose
coordinate derivative evaluations vanish in every chart. For a natural number `p`, this presheaf
of abelian groups sends an analytic open `U` to its holomorphic `p`-forms, with restriction
induced by restriction of functions. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) where
  obj U := AddCommGrpCat.of
    (ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X d U p)
  map {U V} i := AddCommGrpCat.ofHom
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d i p).toAddMonoidHom
  map_id U := by
    apply AddCommGrpCat.hom_ext
    change (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d (𝟙 U) p).toAddMonoidHom = _
    rw [ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction_id]
    rfl
  map_comp i j := by
    apply AddCommGrpCat.hom_ext
    change (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X d (i ≫ j) p).toAddMonoidHom = _
    rw [ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction_comp]
    rfl

/-- Holomorphic differential forms vanish in degrees above the complex dimension, already before
sheafification. -/
private lemma holomorphicDeRhamPresheaf_isZero_of_lt
    [SmoothOfRelativeDimension d X.hom] {p : ℕ} (hp : d < p) :
    IsZero (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d p) := by
  apply Functor.isZero
  intro U
  let : Subsingleton ((ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d p).obj U) :=
    ⟨fun x y => by
      rw [ComplexPoint.Basic.ComplexSchemePoint.holomorphicForm_eq_zero_of_lt X d U hp x,
        ComplexPoint.Basic.ComplexSchemePoint.holomorphicForm_eq_zero_of_lt X d U hp y]⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. Holomorphic
forms are defined as Kähler forms of the algebra of holomorphic functions, modulo forms whose
coordinate derivative evaluations vanish in every chart. This presheaf morphism raises degree
from `p` to `p+1` by exterior differentiation, sending `a₀ da₁ ∧ ⋯ ∧ daₚ` to `da₀ ∧ da₁ ∧ ⋯ ∧
daₚ`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d p ⟶
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d (p + 1) where
  app U := AddCommGrpCat.ofHom <|
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X d U p).toAddMonoidHom
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    ext x
    exact (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction_differential X d i p x).symm

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential_comp [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d p ≫
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d (p + 1) = 0 :=
  NatTrans.ext <| funext fun U => AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun x =>
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential_squared X d U p x

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. Holomorphic
forms are defined as Kähler forms of the algebra of holomorphic functions, modulo forms whose
coordinate derivative evaluations vanish in every chart. This is the nonnegative complex of
presheaves assigning holomorphic `p`-forms to each open in degree `p`, with the exterior
derivative as differential. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheafComplex [SmoothOfRelativeDimension d X.hom] :
    CochainComplex
      (TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) ℕ :=
  CochainComplex.of
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d)
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d)
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential_comp X d)

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheafComplex_d
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheafComplex X d).d p (p + 1) =
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d p := by
  simp [ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheafComplex]

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. This morphism
from the constant complex presheaf to holomorphic zero-forms assigns to `c ∈ ℂ` on each open `U`
the class of the constant function `c` among Kähler zero-forms modulo forms with zero coordinate
evaluations. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero [SmoothOfRelativeDimension d X.hom] :
    𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ⟶ ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d 0 where
  app U := AddCommGrpCat.ofHom
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant X d U).toAddMonoidHom
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    ext c
    exact (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction_ofConstant X d i c).symm

/-- On a nonempty open set, distinct complex constants define distinct holomorphic zero-forms. -/
private lemma holomorphicFormOfConstant_injective [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) [Nonempty U.unop] :
    Function.Injective (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant X d U) := by
  intro c c' hcc'
  have hzero : ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant X d U (c - c') = 0 := by
    rw [map_sub, hcc', sub_self]
  let a : OAI.Algebra.DeRham.Basic.Form ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) 0 :=
    OAI.Algebra.DeRham.Basic.ofConstant ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X d U) (c - c')
  have ha : a ∈ ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X d U 0 := by
    change Submodule.Quotient.mk a = 0 at hzero
    rwa [Submodule.Quotient.mk_eq_zero] at hzero
  let x : U.unop := Classical.arbitrary U.unop
  let e := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x.1
  have hxsource : x.1 ∈ e.source := mem_extChartAt_source x.1
  have hxe : e x.1 ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X d U x.1 := by
    refine ⟨mem_extChartAt_target x.1, ?_⟩
    change e.symm (e x.1) ∈ U.unop
    rw [e.left_inv hxsource]
    exact x.2
  have heval := (ComplexPoint.Basic.ComplexSchemePoint.mem_chartEvaluationKernel_iff X d U 0 a).1 ha
    x.1 (e x.1) hxe
  rw [ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_ofConstant X d U x.1 (c - c') hxe] at heval
  have hcoeff := congrArg
    (fun f : (Fin d → ℂ) [⋀^Fin 0]→L[ℂ] ℂ ↦ f Fin.elim0) heval
  exact sub_eq_zero.mp (by simpa using hcoeff)

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of complex constants into holomorphic zero-forms is a monomorphism on every
stalk. -/
private lemma constantsToHolomorphicDeRhamZero_stalk_mono
    [SmoothOfRelativeDimension d X.hom] (x : ComplexPoint.Basic.ComplexSchemePoint X) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d)) := by
  rw [AddCommGrpCat.mono_iff_injective]
  intro z z' h
  obtain ⟨U, hxU, c, rfl⟩ := 𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ).exists_germ_eq z
  obtain ⟨V, hxV, c', rfl⟩ := 𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ).exists_germ_eq z'
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply] at h
  obtain ⟨W, hxW, iWU, iWV, hW⟩ :=
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d 0).germ_eq x hxU hxV
      ((ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d).app (.op U) c)
      ((ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d).app (.op V) c') h
  let : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hcc' : c = c' := by
    apply holomorphicFormOfConstant_injective X d (.op W)
    have hc := congrArg (fun k :
        𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ).obj (.op U) ⟶
          (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d 0).obj (.op W) ↦ k c)
      ((ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d).naturality iWU.op)
    have hc' := congrArg (fun k :
        𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ).obj (.op V) ⟶
          (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d 0).obj (.op W) ↦ k c')
      ((ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d).naturality iWV.op)
    change ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant X d (.op W) c =
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d 0).map iWU.op
        ((ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d).app (.op U) c) at hc
    change ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormOfConstant X d (.op W) c' =
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d 0).map iWV.op
        ((ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d).app (.op V) c') at hc'
    exact hc.trans (hW.trans hc'.symm)
  subst c'
  rw [← 𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ).germ_res_apply iWU x hxW,
    ← 𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ).germ_res_apply iWV x hxW]
  rfl

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero_comp_differential
    [SmoothOfRelativeDimension d X.hom] :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d ≫
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d 0 = 0 :=
  NatTrans.ext <| funext fun U => AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun c =>
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential_ofConstant X d U c

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. Holomorphic
forms are defined as Kähler forms of the algebra of holomorphic functions, modulo forms whose
coordinate derivative evaluations vanish in every chart. For a natural number `p`, this is the
sheafification, as abelian groups, of the presheaf of holomorphic `p`-forms on analytic opens. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
  (presheafToSheaf J AddCommGrpCat).obj
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d p)

/-- The sheaf of holomorphic `p`-forms is zero for `p` above the complex dimension. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf_isZero_of_lt
    [SmoothOfRelativeDimension d X.hom] {p : ℕ} (hp : d < p) :
    IsZero (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X d p) := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
  exact (presheafToSheaf J AddCommGrpCat).map_isZero
    (holomorphicDeRhamPresheaf_isZero_of_lt X d hp)

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. This is the
sheaf morphism `d: Ω^p → Ω^{p+1}` obtained by sheafifying exterior differentiation of
holomorphic forms. On a local expression it sends `a₀ da₁ ∧ ⋯ ∧ daₚ` to `da₀ ∧ da₁ ∧ ⋯ ∧ daₚ`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X d p ⟶
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X d (p + 1) :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
  (presheafToSheaf J AddCommGrpCat).map
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d p)

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. The holomorphic
de Rham complex is `Ω⁰ → Ω¹ → Ω² → ⋯`, with exterior differentiation. Each term is obtained by
sheafifying Kähler forms of holomorphic functions modulo forms whose coordinate derivative
evaluations vanish in every chart. Degrees are natural numbers. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex [SmoothOfRelativeDimension d X.hom] :
    CochainComplex
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) ℕ :=
  CochainComplex.of
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X d)
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X d)
    (fun p => by
      let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      change (presheafToSheaf J AddCommGrpCat).map
          (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d p) ≫
        (presheafToSheaf J AddCommGrpCat).map
          (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d (p + 1)) = 0
      rw [← Functor.map_comp, ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential_comp, Functor.map_zero])

@[simp] lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex_d [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X d).d p (p + 1) =
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X d p := by
  simp [ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex]

set_option backward.isDefEq.respectTransparency false in
/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. This map of
complexes sends a holomorphic form on an analytic open to its section in the sheaf of such
forms. It is the degreewise sheafification unit of the presheaf de Rham complex, and commutes
with exterior differentiation. -/
noncomputable def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafificationUnit
    [SmoothOfRelativeDimension d X.hom] :
    ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheafComplex X d ⟶
      (TopCat.Sheaf.forget AddCommGrpCat
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).mapHomologicalComplex
          (ComplexShape.up ℕ) |>.obj (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X d) where
  f p := toSheafify
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d p)
  comm' i j hij := by
    obtain rfl := hij
    rw [Functor.mapHomologicalComplex_obj_d, ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheafComplex_d,
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex_d]
    dsimp [ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential, ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf]
    exact (toSheafify_naturality
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d i)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified holomorphic de Rham complex is exact in every positive degree. -/
private lemma holomorphicDeRhamComplex_exactAt_succ
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X d).ExactAt (p + 1) := by
  rw [HomologicalComplex.exactAt_iff'
    (K := ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X d)
    (i := p) (j := p + 1) (k := (p + 1) + 1) (by simp) (by simp)]
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let P := ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheafComplex X d
  have hP : (P.sc' p (p + 1) ((p + 1) + 1)).map stalk |>.Exact :=
    OAI.Topology.Sheaves.StalkExact.TopCat.Presheaf.stalkExact_of_locallyPrimitive
      (P.sc' p (p + 1) ((p + 1) + 1)) (by
        intro y U hyU form hform
        dsimp [P, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'] at hform ⊢
        rw [ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheafComplex_d] at hform
        rw [ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheafComplex_d]
        change ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X d (.op U) (p + 1) form = 0 at hform
        obtain ⟨W, k, θ, hyW, hθ⟩ :=
          ComplexPoint.Basic.ComplexSchemePoint.exists_local_holomorphicForm_primitive X d (.op U) y hyU p form hform
        exact ⟨W.unop, hyW, k.unop, θ, hθ⟩) x
  let unit := ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafificationUnit X d
  let stalkUnit := (stalk.mapHomologicalComplex (ComplexShape.up ℕ)).map unit
  let η := (HomologicalComplex.shortComplexFunctor' AddCommGrpCat
    (ComplexShape.up ℕ) p (p + 1) ((p + 1) + 1)).map stalkUnit
  let : IsIso η.τ₁ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d p)
  let : IsIso η.τ₂ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d (p + 1))
  let : IsIso η.τ₃ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d ((p + 1) + 1))
  let : IsIso η := ShortComplex.isIso_of_isIso η
  exact ShortComplex.exact_of_iso (asIso η) hP

/-- Let `X` be a complex scheme. On its analytic space `X(ℂ)`, this endomorphism of the constant
presheaf of abelian groups with value `ℂ` acts on each open by `c ↦ conj(c)`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexPresheaf :
    𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ⟶ 𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) where
  app _ := AddCommGrpCat.ofHom (starRingEnd ℂ).toAddMonoidHom
  naturality {U V} i := by
    ext x
    rfl

/-- Let `X` be a complex scheme. This endomorphism of the constant complex sheaf on `X(ℂ)`
conjugates locally constant complex-valued functions pointwise. It is additive and
conjugate-linear. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexSheaf :
    𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ⟶ 𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) :=
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
  (presheafToSheaf J AddCommGrpCat).map
    (ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexPresheaf X)

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. This map from
the constant complex sheaf to the sheaf `Ω⁰` of holomorphic zero-forms regards locally constant
complex-valued functions as holomorphic zero-forms. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf [SmoothOfRelativeDimension d X.hom] :
    𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ⟶ ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X d 0 :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
  (presheafToSheaf J AddCommGrpCat).map
    (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d)

lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf_comp_differential
    [SmoothOfRelativeDimension d X.hom] :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf X d ≫
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X d 0 = 0 := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
  change (presheafToSheaf J AddCommGrpCat).map
      (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d) ≫
    (presheafToSheaf J AddCommGrpCat).map
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d 0) = 0
  rw [← Functor.map_comp, ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero_comp_differential,
    Functor.map_zero]

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. This is the
sequence of presheaves `ℂ → Ω⁰ → Ω¹`, where the first arrow sends constants to holomorphic
zero-forms and the second is exterior differentiation. The composite is zero because constants
have zero derivative. -/
noncomputable def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamPresheafShortComplex
    [SmoothOfRelativeDimension d X.hom] :
    ShortComplex (TopCat.Presheaf AddCommGrpCat
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) :=
  ShortComplex.mk (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d)
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d 0)
    (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero_comp_differential X d)

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. This is the
sequence of sheaves `ℂ_X → Ω⁰ → Ω¹`, where `ℂ_X` consists of locally constant functions and the
two arrows are inclusion as holomorphic zero-forms and exterior differentiation. The form
sheaves are obtained by sheafifying the corresponding presheaves. -/
noncomputable def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamSheafShortComplex
    [SmoothOfRelativeDimension d X.hom] :
    ShortComplex (TopCat.Sheaf AddCommGrpCat
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) :=
  ShortComplex.mk (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf X d)
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X d 0)
    (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf_comp_differential X d)

set_option backward.isDefEq.respectTransparency false in
/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. This morphism
sends the presheaf sequence `ℂ → Ω⁰ → Ω¹` to the underlying presheaves of its sheafification.
Each component sends a constant or a holomorphic form to the section represented by its local
germs. -/
noncomputable def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamShortComplexSheafificationUnit
    [SmoothOfRelativeDimension d X.hom] :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamPresheafShortComplex X d ⟶
      (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamSheafShortComplex X d).map
        (TopCat.Sheaf.forget AddCommGrpCat
          (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) where
  τ₁ := toSheafify
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ)
  τ₂ := toSheafify
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d 0)
  τ₃ := toSheafify
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d 1)
  comm₁₂ := (toSheafify_naturality
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZero X d)).symm
  comm₂₃ := (toSheafify_naturality
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamDifferential X d 0)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The augmented holomorphic de Rham sheaf complex is exact. Thus the kernel of the exterior
derivative on holomorphic functions is exactly the constant sheaf. -/
private lemma constantsToHolomorphicDeRhamSheafShortComplex_exact
    [SmoothOfRelativeDimension d X.hom] :
    (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamSheafShortComplex X d).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  have hP : ((ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamPresheafShortComplex X d).map
      stalk).Exact :=
    OAI.Topology.Sheaves.StalkExact.TopCat.Presheaf.stalkExact_of_locallyPrimitive
      (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamPresheafShortComplex X d) (by
        intro y U hyU form hform
        change ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X d (.op U) 0 form = 0 at hform
        obtain ⟨V, i, c, hyV, hi⟩ :=
          ComplexPoint.Basic.ComplexSchemePoint.exists_local_holomorphicForm_eq_constant X d (.op U) y hyU form hform
        exact ⟨V.unop, hyV, i.unop, c, hi.symm⟩) x
  let unit := ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamShortComplexSheafificationUnit X d
  let η := (stalk.mapShortComplex).map unit
  let : IsIso η.τ₁ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ)
  let : IsIso η.τ₂ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d 0)
  let : IsIso η.τ₃ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d 1)
  let : IsIso η := ShortComplex.isIso_of_isIso η
  exact ShortComplex.exact_of_iso (asIso η) hP

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified inclusion of complex constants into holomorphic functions is a
monomorphism. -/
private lemma constantsToHolomorphicDeRhamZeroSheaf_mono
    [SmoothOfRelativeDimension d X.hom] :
    Mono (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf X d) := by
  rw [TopCat.Presheaf.mono_iff_stalk_mono]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let unit := ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamShortComplexSheafificationUnit X d
  let S := (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamPresheafShortComplex X d).map stalk
  let T := (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamSheafShortComplex X d).map
    (TopCat.Sheaf.forget AddCommGrpCat
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ⋙ stalk)
  let η : S ⟶ T := (stalk.mapShortComplex).map unit
  let : IsIso η.τ₁ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      𝓒ᵖ(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ)
  let : IsIso η.τ₂ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamPresheaf X d 0)
  let : Mono S.f := constantsToHolomorphicDeRhamZero_stalk_mono X d x
  change Mono T.f
  have h : T.f = inv η.τ₁ ≫ S.f ≫ η.τ₂ := by
    rw [← cancel_epi η.τ₁, η.comm₁₂]
    simp
  rw [h]
  infer_instance

/-- Let `X` be a smooth complex scheme of dimension `d`, with analytic space `X(ℂ)`. This map of
nonnegative sheaf complexes `ℂ_X[0] → Ω^•` includes locally constant functions as holomorphic
zero-forms. The source is zero in every positive degree, and the target differential is exterior
differentiation. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex [SmoothOfRelativeDimension d X.hom] :
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).obj
        𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ⟶
      ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X d :=
  (CochainComplex.fromSingle₀Equiv (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X d)
    𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ)).symm
      ⟨ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf X d, by
        rw [ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex_d]
        exact ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamZeroSheaf_comp_differential X d⟩

set_option backward.isDefEq.respectTransparency false in
/-- The holomorphic Poincaré lemma identifies the degree-zero de Rham cohomology sheaf with the
constant sheaf. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex_quasiIsoAt_zero
    [SmoothOfRelativeDimension d X.hom] :
    QuasiIsoAt (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X d) 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
  · exact ⟨constantsToHolomorphicDeRhamSheafShortComplex_exact X d,
      constantsToHolomorphicDeRhamZeroSheaf_mono X d⟩
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
/-- The holomorphic Poincaré lemma makes the constant-to-de Rham comparison a
quasi-isomorphism in every positive degree. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex_quasiIsoAt_succ
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    QuasiIsoAt (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X d) (p + 1) := by
  rw [quasiIsoAt_iff_exactAt _ _
    (CochainComplex.exactAt_succ_single_obj 𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) p)]
  exact holomorphicDeRhamComplex_exactAt_succ X d p

/-- The constant sheaf resolves the holomorphic de Rham complex in all natural degrees. -/
instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex_quasiIso
    [SmoothOfRelativeDimension d X.hom] :
    QuasiIso (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X d) where
  quasiIsoAt p := by
    rcases p with _ | p
    · exact ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex_quasiIsoAt_zero X d
    · exact ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex_quasiIsoAt_succ X d p

/-- Let `X` be a complex scheme. This integer-indexed complex of sheaves of abelian groups on `X(ℂ)`
has the constant complex sheaf in degree zero, zero in every other degree, and zero
differentials. -/
@[implicit_reducible]
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt :
    CochainComplex
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) ℤ :=
  ((CochainComplex.single₀
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).obj
      𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ)).extend ComplexShape.embeddingUpNat

/-- Let `X` be a complex scheme. This endomorphism of the nonnegative sheaf complex `ℂ_X[0]`
conjugates locally constant functions in degree zero; every positive-degree term is zero. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexComplex :
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).obj
        𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) ⟶
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).obj
        𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℂ) :=
  (CochainComplex.single₀ _).map (ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexSheaf X)

/-- Let `X` be a complex scheme. This endomorphism of the integer-indexed sheaf complex `ℂ_X[0]`
conjugates locally constant functions in degree zero, with zero terms in all other degrees. It
is additive and conjugate-linear. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexSheafComplexInt :
    ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt X ⟶ ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt X :=
  HomologicalComplex.extendMap (ComplexPoint.Basic.ComplexSchemePoint.conjConstantComplexComplex X)
    ComplexShape.embeddingUpNat

/-- Let `X` be a smooth integral scheme over `ℂ`. This integer-indexed complex on `X(ℂ)` has the
sheaf of holomorphic `p`-forms in each degree `p ≥ 0`, exterior differentiation as differential,
and zero terms in negative degrees. Its charts use the dimension of `X`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplexInt [IsIntegral X.left] [Smooth X.hom] :
    CochainComplex (TopCat.Sheaf AddCommGrpCat ↧(ComplexPoint.Basic.ComplexSchemePoint X)) ℤ :=
  (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)).extend ComplexShape.embeddingUpNat

/-- `Ω•(X)` is the holomorphic de Rham complex of `X(ℂ)`, indexed by the integers. -/
scoped notation:max "Ω•" "(" X ")" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplexInt X

instance [IsIntegral X.left] [Smooth X.hom] :
    CochainComplex.IsStrictlyGE Ω•(X) 0 := by
  unfold ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplexInt
  infer_instance

/-- The integer-indexed holomorphic de Rham complex vanishes in every degree above the complex
dimension. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplexInt_isZero_X_of_lt
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) (hn : (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left : ℤ) < n) :
    IsZero (Ω•(X).X n) := by
  have hn0 : 0 ≤ n := by lia
  let p := n.toNat
  have hp : (p : ℤ) = n := by
    simp [p, Int.toNat_of_nonneg hn0]
  have hdp : OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left < p := by lia
  exact (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf_isZero_of_lt X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) hdp).of_iso
    ((ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)).extendXIso
      ComplexShape.embeddingUpNat hp)

/-- The integer-indexed holomorphic de Rham complex is strictly supported in degrees at most the
complex dimension. -/
noncomputable instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplexInt_isStrictlyLE
    [IsIntegral X.left] [Smooth X.hom] :
    Ω•(X).IsStrictlySupported
      (ComplexShape.embeddingUpIntLE (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)) where
  isZero n hn := by
    rw [ComplexShape.notMem_range_embeddingUpIntLE_iff] at hn
    exact ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplexInt_isZero_X_of_lt X n hn

/-- Let `X` be a smooth integral scheme over `ℂ`. This map `ℂ_X[0] → Ω^•` of integer-indexed sheaf
complexes includes locally constant functions as holomorphic zero-forms. The source is
concentrated in degree zero and the holomorphic de Rham complex is zero in negative degrees. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt [IsIntegral X.left] [Smooth X.hom] :
    ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt X ⟶ Ω•(X) :=
  HomologicalComplex.extendMap
    (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)) ComplexShape.embeddingUpNat

/-- Extending by zero gives the holomorphic de Rham quasi-isomorphism in every integer
degree. -/
instance _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt_quasiIso
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X) := by
  change QuasiIso (HomologicalComplex.extendMap
    (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)) ComplexShape.embeddingUpNat)
  exact (HomologicalComplex.quasiIso_extendMap_iff
    (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex X (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left)) ComplexShape.embeddingUpNat).2
      inferInstance

end

end OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint
