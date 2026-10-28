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
import OAI.Algebra.Homology.DerivedCategoryInjectiveHom
import OAI.Algebra.Homology.Notation

/-! # Hom Postcomp -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HomPostcomp

noncomputable section

/-! # Postcomposition on the Hom complex

The postcomposition counterpart of the upstream precomposition lemmas.
-/

open _root_.CategoryTheory Limits

namespace HomComplex

open _root_.CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Abelian C]
  {K K' : CochainComplex C ℤ} (g : K ⟶ K') (A : CochainComplex C ℤ)

/-- Postcomposition with a chain map, on the Hom complex. -/
def postcompMap : CochainComplex.HomComplex A K ⟶ CochainComplex.HomComplex A K' where
  f n := AddCommGrpCat.ofHom
    { toFun z := z.comp (Cochain.ofHom g) (add_zero n)
      map_zero' := by simp
      map_add' _ _ := Cochain.add_comp _ _ _ _ }
  comm' n m _ := by
    ext z
    exact δ_comp_ofHom z g m

/-- Postcomposition with a chain map, on cocycles. -/
def postcompCocycle (n : ℤ) : Cocycle A K n →+ Cocycle A K' n where
  toFun z := z.postcomp g
  map_zero' := by ext; simp [Cocycle.postcomp]
  map_add' x y := by ext; simp [Cocycle.postcomp, Cochain.add_comp]

/-- Postcomposition with a chain map, on cohomology classes. -/
def postcompClass (n : ℤ) : CohomologyClass A K n →+ CohomologyClass A K' n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom A K' n).comp (postcompCocycle g A n)) (by
      intro z hz
      obtain ⟨m, hm, a, ha⟩ := hz
      change CohomologyClass.mk (z.postcomp g) = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m, hm, a.comp (Cochain.ofHom g) (add_zero m), ?_⟩
      rw [δ_comp_ofHom, ha]
      rfl)

@[simp]
lemma postcompClass_mk (n : ℤ) (z : Cocycle A K n) :
    postcompClass g A n (CohomologyClass.mk z) = CohomologyClass.mk (z.postcomp g) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Postcomposition induces the indicated maps on cycles and cohomology classes. -/
def postcompLeftHomologyMapData (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat ℤᵘᵖ n).map (postcompMap g A))
      (leftHomologyData A K n) (leftHomologyData A K' n) where
  φK := AddCommGrpCat.ofHom (postcompCocycle g A n)
  φH := AddCommGrpCat.ofHom (postcompClass g A n)
  commi := rfl
  commf' := by
    apply (cancel_mono (leftHomologyData A K' n).i).1
    rw [Category.assoc, show
      AddCommGrpCat.ofHom (postcompCocycle g A n) ≫ (leftHomologyData A K' n).i =
        (leftHomologyData A K n).i ≫ (postcompMap g A).f n from rfl,
      ← Category.assoc, ShortComplex.LeftHomologyData.f'_i,
      Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((HomologicalComplex.shortComplexFunctor AddCommGrpCat ℤᵘᵖ n).map
      (postcompMap g A)).comm₁₂.symm
  commπ := rfl

lemma homologyAddEquiv_postcompMap (n : ℤ)
    (x : (CochainComplex.HomComplex A K).homology n) :
    homologyAddEquiv A K' n (HomologicalComplex.homologyMap (postcompMap g A) n x) =
      postcompClass g A n (homologyAddEquiv A K n x) :=
  ConcreteCategory.congr_hom (postcompLeftHomologyMapData g A n).homologyMap_comm x

/-- Evaluation on a single object commutes with postcomposition. -/
lemma postcompMap_fromSingleZeroIsoPreadditiveCoyoneda (B : C) :
    postcompMap g ((CochainComplex.singleFunctor C 0).obj B) ≫
        (Algebra.Homology.HomComplexSingle.CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda B K').hom =
      (Algebra.Homology.HomComplexSingle.CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda B K).hom ≫
        ((preadditiveCoyoneda.obj (.op B)).mapHomologicalComplex ℤᵘᵖ).map g := by
  refine HomologicalComplex.hom_ext _ _ (fun n ↦ ?_)
  apply AddCommGrpCat.hom_ext
  ext z
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z n (zero_add n)
  change Cochain.fromSingleEquiv (zero_add n)
      ((Cochain.fromSingleMk f (zero_add n)).comp (Cochain.ofHom g) (add_zero n)) =
    Cochain.fromSingleEquiv (zero_add n) (Cochain.fromSingleMk f (zero_add n)) ≫ g.f n
  rw [← Cochain.fromSingleMk_postcomp, Cochain.fromSingleEquiv_fromSingleMk,
    Cochain.fromSingleEquiv_fromSingleMk]

end HomComplex

open _root_.CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- A Hom-complex cohomology class gives its actual morphism in the derived category.
This map is defined for every target complex, without an injectivity assumption. -/
def cohomologyClassToDerived (A K : CochainComplex C ℤ) (n : ℤ) :
    CohomologyClass A K n →+
      ShiftedHom (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj K) n :=
  let qSource := (DerivedCategory.quotientCompQhIso C).symm.app A
  let qTarget := (DerivedCategory.Q.commShiftIso n).symm.app K ≪≫
    (DerivedCategory.quotientCompQhIso C).symm.app (K⟦n⟧)
  (Algebra.Homology.DerivedCategoryInjectiveHom.CategoryTheory.isoHomCongrAddEquiv qSource qTarget).symm.toAddMonoidHom.comp <|
    (DerivedCategory.Qh.mapAddHom).comp CohomologyClass.toHom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma cohomologyClassToDerived_mk (A K : CochainComplex C ℤ) (n : ℤ)
    (z : Cocycle A K n) :
    cohomologyClassToDerived A K n (CohomologyClass.mk z) =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q := by
  dsimp [cohomologyClassToDerived, Algebra.Homology.DerivedCategoryInjectiveHom.CategoryTheory.isoHomCongrAddEquiv, ShiftedHom.map]
  rw [CohomologyClass.toHom_mk]
  have h := (DerivedCategory.quotientCompQhIso C).hom.naturality
    (Cocycle.equivHomShift.symm z)
  simp

/-- This canonical map agrees with the inverse K-injective comparison whenever the latter
is defined. -/
lemma cohomologyClassToDerived_kInjective (A I : CochainComplex C ℤ)
    [I.IsKInjective] (n : ℤ) (z : CohomologyClass A I n) :
    cohomologyClassToDerived A I n z =
      (Algebra.Homology.DerivedCategoryInjectiveHom.CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass A I n).symm z := by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [cohomologyClassToDerived_mk,
    Algebra.Homology.DerivedCategoryInjectiveHom.CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk]

/-- Passing from a cohomology class to the derived category respects postcomposition. -/
lemma cohomologyClassToDerived_postcomp {A K L : CochainComplex C ℤ}
    (g : K ⟶ L) (n : ℤ) (z : CohomologyClass A K n) :
    cohomologyClassToDerived A L n (HomPostcomp.HomComplex.postcompClass g A n z) =
      cohomologyClassToDerived A K n z ≫ (DerivedCategory.Q.map g)⟦n⟧' := by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [HomPostcomp.HomComplex.postcompClass_mk, cohomologyClassToDerived_mk,
    cohomologyClassToDerived_mk, Cocycle.equivHomShift_symm_postcomp]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc,
    Functor.commShiftIso_hom_naturality]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HomPostcomp
