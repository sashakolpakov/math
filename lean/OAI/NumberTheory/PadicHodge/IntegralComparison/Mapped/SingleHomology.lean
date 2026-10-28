import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.LeftHomologyIso
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Single Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleHomology

noncomputable section

/-! The surviving homology coordinate of a single complex commutes
with an exact additive functor and with maps into that complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  (N : C) (n : ℕ)

def zeroData : (((single C (.up ℕ) n).obj N).sc n).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofZeros _ (by simp) (by simp)

theorem zeroData_coordinate :
    (zeroData N n).homologyIso.hom ≫ (singleObjXSelf (.up ℕ) n N).hom =
      (singleObjHomologySelfIso (.up ℕ) n N).hom := by
  apply (cancel_epi (((single C (.up ℕ) n).obj N).homologyπ n)).mp
  have hc : (zeroData N n).cyclesIso.hom =
      (((single C (.up ℕ) n).obj N).sc n).iCycles := by
    have h := (zeroData N n).cyclesIso_hom_comp_i
    change (zeroData N n).cyclesIso.hom ≫ 𝟙 _ = _ at h
    simpa only [Category.comp_id] using h
  erw [← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
    homologyπ_singleObjHomologySelfIso_hom, singleObjCyclesSelfIso_hom]
  change ((zeroData N n).cyclesIso.hom ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id, hc]
  rfl

theorem single :
    homologyMap ((singleMapHomologicalComplex F (.up ℕ) n).hom.app N) n ≫
        (singleObjHomologySelfIso (.up ℕ) n (F.obj N)).hom =
      ((((HomologicalComplex.single C (.up ℕ) n).obj N).sc n).mapHomologyIso F).hom ≫
        F.map (singleObjHomologySelfIso (.up ℕ) n N).hom := by
  let K := (HomologicalComplex.single C (.up ℕ) n).obj N
  let L := (F.mapHomologicalComplex (.up ℕ)).obj K
  let a := (singleMapHomologicalComplex F (.up ℕ) n).hom.app N
  have he : ((K.sc n).mapHomologyIso F).hom ≫
      F.map (singleObjHomologySelfIso (.up ℕ) n N).hom =
      ((zeroData N n).map F).homologyIso.hom ≫
        F.map (singleObjXSelf (.up ℕ) n N).hom := by
    calc
      _ = ((K.sc n).mapHomologyIso F).hom ≫
          F.map ((zeroData N n).homologyIso.hom ≫ (singleObjXSelf (.up ℕ) n N).hom) :=
        congrArg (fun z => ((K.sc n).mapHomologyIso F).hom ≫ F.map z)
          (zeroData_coordinate N n).symm
      _ = (((K.sc n).mapHomologyIso F).hom ≫ F.map (zeroData N n).homologyIso.hom) ≫
          F.map (singleObjXSelf (.up ℕ) n N).hom := by rw [F.map_comp, Category.assoc]
      _ = _ := congrArg (fun z => z ≫ F.map (singleObjXSelf (.up ℕ) n N).hom)
        (AlgebraicGeometry.Crystalline.Cohomology.Mapped.LeftHomologyIso.MappedLeftHomologyIso.homologyIso F (K.sc n) (zeroData N n))
  apply Eq.trans ?_ he.symm
  apply (cancel_epi (L.homologyπ n)).mp
  have hc : ((zeroData N n).map F).cyclesIso.hom =
      ((((HomologicalComplex.single C (.up ℕ) n).obj N).sc n).map F).iCycles := by
    have h := ((zeroData N n).map F).cyclesIso_hom_comp_i
    change ((zeroData N n).map F).cyclesIso.hom ≫ F.map (𝟙 _) = _ at h
    erw [F.map_id, Category.comp_id] at h
    exact h
  have hπ : L.homologyπ n ≫ ((zeroData N n).map F).homologyIso.hom = L.iCycles n := by
    have h := ((zeroData N n).map F).homologyπ_comp_homologyIso_hom
    change L.homologyπ n ≫ ((zeroData N n).map F).homologyIso.hom =
      ((zeroData N n).map F).cyclesIso.hom ≫ F.map (𝟙 _) at h
    erw [F.map_id, Category.comp_id, hc] at h
    exact h
  have ht : a.f n ≫ (singleObjXSelf (.up ℕ) n (F.obj N)).hom =
      F.map (singleObjXSelf (.up ℕ) n N).hom := by
    dsimp only [a]
    rw [singleMapHomologicalComplex_hom_app_self, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hi : cyclesMap a n ≫
      ((HomologicalComplex.single D (.up ℕ) n).obj (F.obj N)).iCycles n =
      L.iCycles n ≫ a.f n := cyclesMap_i a n
  calc
    _ = (L.homologyπ n ≫ homologyMap a n) ≫
        (singleObjHomologySelfIso (.up ℕ) n (F.obj N)).hom := (Category.assoc _ _ _).symm
    _ = (cyclesMap a n ≫ ((HomologicalComplex.single D (.up ℕ) n).obj
        (F.obj N)).homologyπ n) ≫ (singleObjHomologySelfIso (.up ℕ) n (F.obj N)).hom :=
      congrArg (fun z => z ≫ (singleObjHomologySelfIso (.up ℕ) n (F.obj N)).hom)
        (homologyπ_naturality a n)
    _ = cyclesMap a n ≫
        (((HomologicalComplex.single D (.up ℕ) n).obj (F.obj N)).iCycles n ≫
          (singleObjXSelf (.up ℕ) n (F.obj N)).hom) := by
      rw [Category.assoc, homologyπ_singleObjHomologySelfIso_hom, singleObjCyclesSelfIso_hom]
    _ = L.iCycles n ≫ (a.f n ≫ (singleObjXSelf (.up ℕ) n (F.obj N)).hom) := by
      rw [← Category.assoc, hi, Category.assoc]
    _ = L.iCycles n ≫ F.map (singleObjXSelf (.up ℕ) n N).hom := congrArg _ ht
    _ = _ := by rw [← Category.assoc, hπ]

variable (K : CochainComplex C ℕ)
  (a : K ⟶ (HomologicalComplex.single C (.up ℕ) n).obj N)

theorem map :
    homologyMap (SingleCoordinates.map F K N n a) n ≫
        (singleObjHomologySelfIso (.up ℕ) n (F.obj N)).hom =
      ((K.sc n).mapHomologyIso F).hom ≫
        F.map (homologyMap a n ≫ (singleObjHomologySelfIso (.up ℕ) n N).hom) := by
  have h := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor C (.up ℕ) n).map a) F
  change homologyMap ((F.mapHomologicalComplex (.up ℕ)).map a) n ≫
      ((((HomologicalComplex.single C (.up ℕ) n).obj N).sc n).mapHomologyIso F).hom =
        ((K.sc n).mapHomologyIso F).hom ≫ F.map (homologyMap a n) at h
  calc
    _ = homologyMap ((F.mapHomologicalComplex (.up ℕ)).map a) n ≫
        (homologyMap ((singleMapHomologicalComplex F (.up ℕ) n).hom.app N) n ≫
          (singleObjHomologySelfIso (.up ℕ) n (F.obj N)).hom) := by
      rw [SingleCoordinates.map, homologyMap_comp, Category.assoc]
    _ = _ := by
      rw [Mapped.SingleHomology.single]
      calc
        _ = (homologyMap ((F.mapHomologicalComplex (.up ℕ)).map a) n ≫
            ((((HomologicalComplex.single C (.up ℕ) n).obj N).sc n).mapHomologyIso F).hom) ≫
              F.map (singleObjHomologySelfIso (.up ℕ) n N).hom := (Category.assoc _ _ _).symm
        _ = (((K.sc n).mapHomologyIso F).hom ≫ F.map (homologyMap a n)) ≫
            F.map (singleObjHomologySelfIso (.up ℕ) n N).hom :=
          congrArg (fun z => z ≫ F.map (singleObjHomologySelfIso (.up ℕ) n N).hom) h
        _ = _ := by rw [F.map_comp, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleHomology
