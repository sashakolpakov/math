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
import OAI.Algebra.Homology.Notation
import OAI.AlgebraicTopology.Sheaf.Constant
import OAI.AlgebraicGeometry.Cohomology.SingularSheafComparison
import OAI.AlgebraicTopology.Sheaf.FlasqueQuasiIso
import OAI.AlgebraicTopology.Sheaf.InjectiveFlasque
import OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain
import OAI.Algebra.Homology.MapExtend
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.Factorizations.CM5a
import OAI.Algebra.Homology.HomComplexSingle
import OAI.CategoryTheory.ConcreteCategory.Notation

/-! # Global Sections -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry
open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Singular cohomology and global sections

This file identifies rational singular cohomology with the cohomology of the global-section
complex of the sheafified singular-cochain resolution on a paracompact Hausdorff space. It also
computes the hypercohomology of that resolution on a hereditarily paracompact Hausdorff space.

The derived comparison uses a bounded-below termwise-injective replacement. The mapping-cone
argument in `Sheaf.FlasqueQuasiIso` proves that its quasi-isomorphism remains a
quasi-isomorphism after taking global sections.
-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace

namespace Cohomology.GlobalSections.TopCat.Sheaf

section

variable {Y : TopCat.{0}}

/-- Let `Y` be a topological space and `F` a sheaf of abelian groups on `Y`. This additive
equivalence `Hom(ℤ_Y, F) ≃ Γ(Y, F)` evaluates a sheaf morphism at the constant global section
`1`. Its inverse sends a section `s` to the morphism taking each locally constant integer to the
corresponding multiple of `s`. -/
def integerConstantHomAddEquivGlobalSections
    (F : TopCat.Sheaf AddCommGrpCat Y) :
    letI : AddCommGroup ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).obj (AddCommGrpCat.of ℤ) ⟶ F) :=
      (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat Y)).homGroup _ _
    ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).obj (AddCommGrpCat.of ℤ) ⟶ F) ≃+ F.presheaf.obj (.op (⊤ : Opens Y)) := by
  letI : AddCommGroup ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).obj (AddCommGrpCat.of ℤ) ⟶ F) :=
    (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat Y)).homGroup _ _
  exact ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat
      isTerminalTop).homAddEquiv (AddCommGrpCat.of ℤ) F).trans <|
    AddCommGrpCat.homAddEquiv.trans (zmultiplesAddHom (F.presheaf.obj (.op ⊤))).symm

/-- The constant-integer/global-sections equivalence is natural in the sheaf. -/
lemma integerConstantHomAddEquivGlobalSections_naturality
    {F G : TopCat.Sheaf AddCommGrpCat Y} (f : F ⟶ G)
    (g : (AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).obj (AddCommGrpCat.of ℤ) ⟶ F) :
    integerConstantHomAddEquivGlobalSections G (g ≫ f) =
      f.hom.app (.op (⊤ : Opens Y))
        (integerConstantHomAddEquivGlobalSections F g) := rfl

end

/-- Let `Y` be a topological space. This integer-indexed complex of sheaves of abelian groups on `Y`
has the constant integer sheaf `ℤ_Y` in degree zero, zero sheaves in every other degree, and
zero differentials. -/
def integerConstantSingleComplex (Y : TopCat.{0}) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ :=
  (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat Y) 0).obj
    ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).obj (AddCommGrpCat.of ℤ))

/-- Let `Y` be a topological space and `K` an integer-indexed complex of sheaves of abelian groups
on `Y`. The complex `Γ(Y, K)` has `Γ(Y, K^n)` in degree `n`; its differentials are the maps on
global sections induced by those of `K`. -/
def globalSectionsComplexInt (Y : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) :
    -- `Γ(Y, K^•)`.
    CochainComplex AddCommGrpCat ℤ :=
  AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsComplex K

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let `Y` be a topological space. This natural isomorphism identifies the functors `F ↦ Hom(ℤ_Y,
F)` and `F ↦ Γ(Y, F)` on sheaves of abelian groups, by evaluating each morphism at the constant
section `1`. -/
def integerConstantHomIsoGlobalSectionsFunctor (Y : TopCat.{0}) :
    preadditiveCoyoneda.obj (.op ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).obj (AddCommGrpCat.of ℤ))) ≅
      AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y :=
  NatIso.ofComponents
    (fun F ↦ (integerConstantHomAddEquivGlobalSections F).toAddCommGrpIso)
    (fun {F G} f ↦ by
      apply AddCommGrpCat.hom_ext
      ext g
      change f.hom.app (.op (⊤ : Opens Y))
          (integerConstantHomAddEquivGlobalSections F g) =
        integerConstantHomAddEquivGlobalSections G (g ≫ f)
      exact (integerConstantHomAddEquivGlobalSections_naturality f g).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let `Y` be a topological space and `K` an integer-indexed complex of sheaves of abelian groups.
Evaluation at `1` gives this isomorphism of complexes `Hom^•(ℤ_Y[0], K) ≅ Γ(Y, K)`. -/
def homComplexSingleIntegerIsoGlobalSections
    (Y : TopCat.{0}) (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) :
    CochainComplex.HomComplex (integerConstantSingleComplex Y) K ≅
      globalSectionsComplexInt Y K :=
  let pre := (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat Y))
  letI : Preadditive (TopCat.Sheaf AddCommGrpCat Y) := pre
  letI : (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  OAI.Algebra.Homology.HomComplexSingle.CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda
      ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).obj (AddCommGrpCat.of ℤ)) K ≪≫
    (NatIso.mapHomologicalComplex (integerConstantHomIsoGlobalSectionsFunctor Y)
      ℤᵘᵖ).app K

end Cohomology.GlobalSections.TopCat.Sheaf

open OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (X : Over (Spec ↧ℂ))

local instance ComplexPoint.Basic.ComplexSchemePoint.bettiGlobalSectionsHasDerivedCategory :
    HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)

/-- Let `X` be a scheme over `ℂ`. This identifies two complexes on its analytic space: the constant
integer sheaf in degree zero first indexed by natural numbers and then extended by zero, and the
same sheaf placed directly in degree zero of an integer-indexed complex. -/
def ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle :
    ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X ≅
      Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); ℤ) 0 0 rfl

end

end OAI.AlgebraicGeometry
