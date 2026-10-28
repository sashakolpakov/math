import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.SingleHomology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomologyNaturality
import Mathlib.Algebra.Homology.QuasiIso

/-! # Augmented Homology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.AugmentedHomology.MappedAugmentedHomology

noncomputable section

/-! # Exact transport of the degree-zero comparison for an augmented resolution -/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  {A : C} {K : CochainComplex C ℕ}
  (α : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIsoAt α 0]

def augmentation : (CochainComplex.single₀ D).obj (F.obj A) ⟶
    (F.mapHomologicalComplex (.up ℕ)).obj K :=
  SingleHomology.MappedSingleHomology.singleMap F A ≫ (F.mapHomologicalComplex (.up ℕ)).map α

theorem comparison : HomologicalComplex.homologyMap (augmentation F α) 0 ≫
      (ComplexHomology.MappedComplexHomology.iso F K 0).hom ≫
        F.map ((isoOfQuasiIsoAt α 0).inv ≫ (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 A).hom) =
    (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 (F.obj A)).hom := by
  let HC := HomologicalComplex.homologyFunctor C (.up ℕ) 0
  let HD := HomologicalComplex.homologyFunctor D (.up ℕ) 0
  let P := (CochainComplex.single₀ C).obj A
  let e : HC.obj P ≅ HC.obj K := isoOfQuasiIsoAt α 0
  let s : HC.obj P ≅ A := HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 A
  let sD : HD.obj ((CochainComplex.single₀ D).obj (F.obj A)) ≅ F.obj A :=
    HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 (F.obj A)
  let tP : HD.obj ((F.mapHomologicalComplex (.up ℕ)).obj P) ≅ F.obj (HC.obj P) :=
    ComplexHomology.MappedComplexHomology.iso F P 0
  let tK : HD.obj ((F.mapHomologicalComplex (.up ℕ)).obj K) ≅ F.obj (HC.obj K) :=
    ComplexHomology.MappedComplexHomology.iso F K 0
  let u := HD.map (SingleHomology.MappedSingleHomology.singleMap F A)
  let v := HD.map ((F.mapHomologicalComplex (.up ℕ)).map α)
  have hv : v ≫ tK.hom = tP.hom ≫ F.map e.hom :=
    ComplexHomologyNaturality.MappedComplexHomologyNaturality.naturality F α 0
  have hmap : HD.map (augmentation F α) = u ≫ v :=
    HD.map_comp (SingleHomology.MappedSingleHomology.singleMap F A) ((F.mapHomologicalComplex (.up ℕ)).map α)
  change HD.map (augmentation F α) ≫ tK.hom ≫ F.map (e.inv ≫ s.hom) = sD.hom
  rw [hmap, F.map_comp]
  calc
    (u ≫ v) ≫ tK.hom ≫ F.map e.inv ≫ F.map s.hom =
        u ≫ (v ≫ tK.hom) ≫ F.map e.inv ≫ F.map s.hom := by simp only [Category.assoc]
    _ = u ≫ (tP.hom ≫ F.map e.hom) ≫ F.map e.inv ≫ F.map s.hom := by rw [hv]
    _ = u ≫ tP.hom ≫ F.map s.hom := by
      let y := F.mapIso e
      change u ≫ (tP.hom ≫ y.hom) ≫ y.inv ≫ F.map s.hom = _
      rw [Category.assoc, Iso.hom_inv_id_assoc]
    _ = sD.hom := SingleHomology.MappedSingleHomology.naturality F A

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.AugmentedHomology.MappedAugmentedHomology
