/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafDerivedGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedCochainNaturality

/-! # Represented Cohomology Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedCohomologyMaps.DerivedSections

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.CategoryTheory.Abelian.Ext
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {G : C ⥤ AddCommGrpCat.{v}} [G.Additive]
variable {Z F : C}

def cocyclePostcomp {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    CochainComplex.HomComplex.Cocycle ((CochainComplex.singleFunctor C 0).obj Z) K n →+
      CochainComplex.HomComplex.Cocycle ((CochainComplex.singleFunctor C 0).obj Z) L n where
  toFun z := z.postcomp f
  map_zero' := by ext; simp [CochainComplex.HomComplex.Cocycle.postcomp]
  map_add' x y := by ext; simp [CochainComplex.HomComplex.Cocycle.postcomp]

def cohomologyClassPostcomp {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor C 0).obj Z) K n →+
      CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor C 0).obj Z) L n :=
  CochainComplex.HomComplex.CohomologyClass.descAddMonoidHom
    ((CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom
      ((CochainComplex.singleFunctor C 0).obj Z) L n).comp (cocyclePostcomp f n)) (by
        rintro z ⟨m, hm, β, hβ⟩
        rw [AddMonoidHom.mem_ker]
        change CochainComplex.HomComplex.CohomologyClass.mk (z.postcomp f) = 0
        rw [CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff]
        refine ⟨m, hm, β.comp (.ofHom f) (add_zero m), ?_⟩
        rw [CochainComplex.HomComplex.Cocycle.postcomp_coe, ← hβ]
        exact CochainComplex.HomComplex.δ_comp_ofHom β f n)

lemma cohomologyClassPostcomp_mk {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (n : ℤ)
    (z : CochainComplex.HomComplex.Cocycle
      ((CochainComplex.singleFunctor C 0).obj Z) K n) :
    cohomologyClassPostcomp f n (CochainComplex.HomComplex.CohomologyClass.mk z) =
      CochainComplex.HomComplex.CohomologyClass.mk (z.postcomp f) :=
  rfl

def homComplexPostcompLeftHomologyMapData {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v} (.up ℤ) n).map
        (RepresentedCochainNaturality.DerivedSections.homComplexPostcomp f))
      (CochainComplex.HomComplex.leftHomologyData
        ((CochainComplex.singleFunctor C 0).obj Z) K n)
      (CochainComplex.HomComplex.leftHomologyData
        ((CochainComplex.singleFunctor C 0).obj Z) L n) where
  φK := AddCommGrpCat.ofHom (cocyclePostcomp f n)
  φH := AddCommGrpCat.ofHom (cohomologyClassPostcomp f n)
  commi := by ext; rfl
  commf' := by
    let hK := CochainComplex.HomComplex.leftHomologyData
      ((CochainComplex.singleFunctor C 0).obj Z) K n
    let hL := CochainComplex.HomComplex.leftHomologyData
      ((CochainComplex.singleFunctor C 0).obj Z) L n
    let φ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v} (.up ℤ) n).map
      (RepresentedCochainNaturality.DerivedSections.homComplexPostcomp (Z := Z) f)
    let φK : hK.K ⟶ hL.K := AddCommGrpCat.ofHom (cocyclePostcomp f n)
    change hK.f' ≫ φK = φ.τ₁ ≫ hL.f'
    have hcommi : φK ≫ hL.i = hK.i ≫ φ.τ₂ := by
      ext
      rfl
    apply (cancel_mono hL.i).1
    calc
      (hK.f' ≫ φK) ≫ hL.i = hK.f' ≫ hK.i ≫ φ.τ₂ := by
        rw [Category.assoc, hcommi]
      _ = ((((CochainComplex.singleFunctor C 0).obj Z).HomComplex K).sc n).f ≫
          φ.τ₂ := by rw [← Category.assoc, hK.f'_i]
      _ = φ.τ₁ ≫ ((((CochainComplex.singleFunctor C 0).obj Z).HomComplex L).sc n).f :=
        φ.comm₁₂.symm
      _ = (φ.τ₁ ≫ hL.f') ≫ hL.i := by rw [Category.assoc, hL.f'_i]
  commπ := by ext; rfl

lemma homologyAddEquiv_homComplexPostcomp {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (n : ℤ)
    (x : ↑((((CochainComplex.singleFunctor C 0).obj Z).HomComplex K).homology n)) :
    CochainComplex.HomComplex.homologyAddEquiv
        ((CochainComplex.singleFunctor C 0).obj Z) L n
        (((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).map
          (RepresentedCochainNaturality.DerivedSections.homComplexPostcomp f)).hom x) =
      cohomologyClassPostcomp f n
        (CochainComplex.HomComplex.homologyAddEquiv
          ((CochainComplex.singleFunctor C 0).obj Z) K n x) := by
  rw [HomologicalComplex.homologyFunctor_map]
  let hK := CochainComplex.HomComplex.leftHomologyData
    ((CochainComplex.singleFunctor C 0).obj Z) K n
  let hL := CochainComplex.HomComplex.leftHomologyData
    ((CochainComplex.singleFunctor C 0).obj Z) L n
  let φ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v} (.up ℤ) n).map
    (RepresentedCochainNaturality.DerivedSections.homComplexPostcomp (Z := Z) f)
  let γ := homComplexPostcompLeftHomologyMapData (Z := Z) f n
  change (hL.homologyIso.hom).hom ((ShortComplex.homologyMap φ).hom x) =
    (AddCommGrpCat.ofHom (cohomologyClassPostcomp f n)).hom ((hK.homologyIso.hom).hom x)
  exact ConcreteCategory.congr_hom γ.homologyMap_comm x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedCohomologyMaps.DerivedSections
