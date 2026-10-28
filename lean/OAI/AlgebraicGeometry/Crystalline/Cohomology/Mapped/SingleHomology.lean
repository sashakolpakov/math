import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ZeroHomology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology
import Mathlib.Algebra.Homology.Additive

/-! # Single Homology -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.SingleHomology.MappedSingleHomology

noncomputable section

/-! # The original single-complex homology isomorphism commutes with exact functors -/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (A : C)

def singleMap : (CochainComplex.single₀ D).obj (F.obj A) ⟶
    (F.mapHomologicalComplex (.up ℕ)).obj ((CochainComplex.single₀ C).obj A) :=
  (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).inv.app A

theorem naturality : HomologicalComplex.homologyMap (singleMap F A) 0 ≫
      (ComplexHomology.MappedComplexHomology.iso F ((CochainComplex.single₀ C).obj A) 0).hom ≫
        F.map (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 A).hom =
    (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 (F.obj A)).hom := by
  let KC := (CochainComplex.single₀ C).obj A
  let KD := (CochainComplex.single₀ D).obj (F.obj A)
  let eC : KC.homology 0 ≅ KC.X 0 := (ZeroHomology.MappedZeroHomology.singleData A).homologyIso
  let eD : KD.homology 0 ≅ KD.X 0 := (ZeroHomology.MappedZeroHomology.singleData (F.obj A)).homologyIso
  let xC : KC.X 0 ≅ A := HomologicalComplex.singleObjXSelf (.up ℕ) 0 A
  let xD : KD.X 0 ≅ F.obj A := HomologicalComplex.singleObjXSelf (.up ℕ) 0 (F.obj A)
  let sC : KC.homology 0 ≅ A := HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 A
  let sD : KD.homology 0 ≅ F.obj A := HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 (F.obj A)
  let t := (ComplexHomology.MappedComplexHomology.iso F KC 0).hom
  let z := HomologicalComplex.homologyMap (singleMap F A) 0
  let u : KD.X 0 ⟶ F.obj (KC.X 0) := (singleMap F A).f 0
  have hz : z ≫ t ≫ F.map eC.hom = eD.hom ≫ u :=
    ZeroHomology.MappedZeroHomology.naturality F (KC.sc 0) (KD.sc 0)
      ((HomologicalComplex.shortComplexFunctor D (.up ℕ) 0).map (singleMap F A)) rfl rfl rfl rfl
  have hu : u = xD.hom ≫ F.map xC.inv :=
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self F (.up ℕ) 0 A
  have hC : eC.hom ≫ xC.hom = sC.hom := ZeroHomology.MappedZeroHomology.singleData_original A
  have hD : eD.hom ≫ xD.hom = sD.hom := ZeroHomology.MappedZeroHomology.singleData_original (F.obj A)
  change z ≫ t ≫ F.map sC.hom = sD.hom
  calc
    z ≫ t ≫ F.map sC.hom = (z ≫ t ≫ F.map eC.hom) ≫ F.map xC.hom := by
      rw [← hC, F.map_comp]
      simp only [Category.assoc]
    _ = (eD.hom ≫ u) ≫ F.map xC.hom :=
      congrArg (fun f : KD.homology 0 ⟶ F.obj (KC.X 0) => f ≫ F.map xC.hom) hz
    _ = eD.hom ≫ xD.hom := by
      rw [hu]
      let y := F.mapIso xC
      change (eD.hom ≫ (xD.hom ≫ y.inv)) ≫ y.hom = eD.hom ≫ xD.hom
      rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = sD.hom := hD

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.SingleHomology.MappedSingleHomology
