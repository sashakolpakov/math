/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafDerivedGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedComplexExtensionNaturality

/-! # Ext Injective Homology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtInjectiveHomology.DerivedSections

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.CategoryTheory.Abelian.Ext
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {G : C ⥤ AddCommGrpCat.{v}} [G.Additive]
variable {Z F : C}

def extAddEquivHomComplexHomology
    [HasExt.{v} C] (R : InjectiveResolution F) (n : ℕ) :
    Ext.{v} Z F n ≃+
      ↑((((CochainComplex.singleFunctor C 0).obj Z).HomComplex R.cochainComplex).homology n) :=
  (R.extAddEquivCohomologyClass (X := Z)).trans
    (CochainComplex.HomComplex.homologyAddEquiv
      ((CochainComplex.singleFunctor C 0).obj Z) R.cochainComplex n).symm

lemma extAddEquivHomComplexHomology_naturality
    [HasExt.{v} C] {F' : C} (R : InjectiveResolution F) (R' : InjectiveResolution F')
    (g : F ⟶ F') (φ : InjectiveResolution.Hom R R' g) (n : ℕ) (x : Ext.{v} Z F n) :
    extAddEquivHomComplexHomology R' n (x.comp (Ext.mk₀ g) (add_zero n)) =
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).map
        (RepresentedCochainNaturality.DerivedSections.homComplexPostcomp φ.hom')).hom (extAddEquivHomComplexHomology R n x) := by
  obtain ⟨a, ha, rfl⟩ := R.extMk_surjective x (n + 1) rfl
  rw [R.extMk_comp_mk₀ a (n + 1) rfl ha φ]
  apply (CochainComplex.HomComplex.homologyAddEquiv
    ((CochainComplex.singleFunctor C 0).obj Z) R'.cochainComplex n).injective
  rw [RepresentedCohomologyMaps.DerivedSections.homologyAddEquiv_homComplexPostcomp]
  simp only [extAddEquivHomComplexHomology, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply, InjectiveResolution.extAddEquivCohomologyClass_apply,
    InjectiveResolution.extEquivCohomologyClass_extMk, RepresentedCohomologyMaps.DerivedSections.cohomologyClassPostcomp_mk]
  congr 1
  have hcomp : (a ≫ φ.hom.f n) ≫ (R'.cochainComplexXIso n n (by lia)).inv =
      (a ≫ (R.cochainComplexXIso n n (by lia)).inv) ≫ φ.hom'.f n := by
    simp [φ.hom'_f n n rfl]
  rw [← CochainComplex.HomComplex.Cocycle.fromSingleMk_postcomp
    (a ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add (n : ℤ))
      ((n + 1 : ℕ) : ℤ) (by lia) (by
        rw [R.cochainComplex_d (n : ℤ) ((n + 1 : ℕ) : ℤ) n (n + 1) rfl rfl]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← Category.assoc, ha]
        simp) φ.hom']
  ext : 1
  simp only [CochainComplex.HomComplex.Cocycle.fromSingleMk_coe]
  exact congrArg
    (fun t ↦ CochainComplex.HomComplex.Cochain.fromSingleMk t (zero_add (n : ℤ))) hcomp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtInjectiveHomology.DerivedSections
