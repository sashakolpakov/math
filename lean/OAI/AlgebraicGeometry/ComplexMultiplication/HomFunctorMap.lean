import OAI.AlgebraicGeometry.ComplexMultiplication.HomPostcomp

/-! # Hom Functor Map -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HomFunctorMap.HomComplex

noncomputable section

/-! # Actual additive functors on Hom-complex cohomology classes

This supplies the cochain-level map used to compare actual inverse image with
the original global-section-to-hypercohomology construction.
-/

open _root_.CategoryTheory Limits

universe v u₁ u₂

open _root_.CochainComplex.HomComplex

variable {C : Type u₁} {D : Type u₂} [Category.{v} C] [Abelian C]
  [Category.{v} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] (A K : CochainComplex C ℤ)

/-- The actual componentwise functorial map on the Hom complex. -/
def functorMap : CochainComplex.HomComplex A K ⟶
    CochainComplex.HomComplex ((F.mapHomologicalComplex _).obj A)
      ((F.mapHomologicalComplex _).obj K) where
  f n := AddCommGrpCat.ofHom
    { toFun z := z.map F
      map_zero' := Cochain.map_zero _ _ _ F
      map_add' z z' := Cochain.map_add z z' F }
  comm' n m _ := by
    ext z
    exact δ_map n m z F

/-- Actual functorial mapping of cocycles. -/
def functorMapCocycle (n : ℤ) : Cocycle A K n →+
    Cocycle ((F.mapHomologicalComplex _).obj A) ((F.mapHomologicalComplex _).obj K) n where
  toFun z := ⟨z.val.map F, by
    have hz := z.property
    rw [Cocycle.mem_iff n (n + 1) rfl] at hz ⊢
    rw [δ_map, hz, Cochain.map_zero]⟩
  map_zero' := by
    apply Cocycle.ext
    exact Cochain.map_zero _ _ _ F
  map_add' z z' := by
    apply Cocycle.ext
    exact Cochain.map_add z.val z'.val F

/-- Actual functorial mapping of Hom-complex cohomology classes. -/
def functorMapClass (n : ℤ) : CohomologyClass A K n →+
    CohomologyClass ((F.mapHomologicalComplex _).obj A)
      ((F.mapHomologicalComplex _).obj K) n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom _ _ n).comp (functorMapCocycle F A K n)) (by
      intro z hz
      obtain ⟨m, hm, a, ha⟩ := hz
      change CohomologyClass.mk (functorMapCocycle F A K n z) = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m, hm, a.map F, ?_⟩
      rw [δ_map, ha]
      rfl)

@[simp]
theorem functorMapClass_mk (n : ℤ) (z : Cocycle A K n) :
    functorMapClass F A K n (CohomologyClass.mk z) =
      CohomologyClass.mk (functorMapCocycle F A K n z) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Mapping the actual Hom complex gives exactly these maps on cycles and classes. -/
def functorMapLeftHomologyMapData (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n).map
        (functorMap F A K))
      (leftHomologyData A K n)
      (leftHomologyData ((F.mapHomologicalComplex _).obj A)
        ((F.mapHomologicalComplex _).obj K) n) where
  φK := AddCommGrpCat.ofHom (functorMapCocycle F A K n)
  φH := AddCommGrpCat.ofHom (functorMapClass F A K n)
  commi := rfl
  commf' := by
    apply (cancel_mono (leftHomologyData ((F.mapHomologicalComplex _).obj A)
      ((F.mapHomologicalComplex _).obj K) n).i).1
    rw [Category.assoc, show
      AddCommGrpCat.ofHom (functorMapCocycle F A K n) ≫
          (leftHomologyData ((F.mapHomologicalComplex _).obj A)
            ((F.mapHomologicalComplex _).obj K) n).i =
        (leftHomologyData A K n).i ≫ (functorMap F A K).f n from rfl,
      ← Category.assoc, ShortComplex.LeftHomologyData.f'_i,
      Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n).map
      (functorMap F A K)).comm₁₂.symm
  commπ := rfl

/-- Actual Hom-complex homology and cohomology-class maps commute. -/
theorem homologyAddEquiv_functorMap (n : ℤ) (z : (CochainComplex.HomComplex A K).homology n) :
    homologyAddEquiv ((F.mapHomologicalComplex _).obj A) ((F.mapHomologicalComplex _).obj K) n
        (HomologicalComplex.homologyMap (functorMap F A K) n z) =
      functorMapClass F A K n (homologyAddEquiv A K n z) :=
  ConcreteCategory.congr_hom (functorMapLeftHomologyMapData F A K n).homologyMap_comm z

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HomFunctorMap.HomComplex
