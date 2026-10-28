import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleHomology

/-! # Single Left Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleLeftHomology

noncomputable section

/-! The single-complex homology coordinate requires preservation only
of its own left homology data. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]

private theorem homologyIso (S : ShortComplex C) [F.PreservesLeftHomologyOf S]
    (d : S.LeftHomologyData) :
    (S.mapHomologyIso F).hom ≫ F.map d.homologyIso.hom =
      (d.map F).homologyIso.hom := by
  rw [d.mapHomologyIso_eq F]
  change (((d.map F).homologyIso.hom ≫ (F.mapIso d.homologyIso).inv) ≫
    (F.mapIso d.homologyIso).hom) = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

open OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleHomology
variable (N : C) (n : ℕ)

variable [F.PreservesLeftHomologyOf (((single C (.up ℕ) n).obj N).sc n)]

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
      ((SingleHomology.zeroData N n).map F).homologyIso.hom ≫
        F.map (singleObjXSelf (.up ℕ) n N).hom := by
    calc
      _ = ((K.sc n).mapHomologyIso F).hom ≫
          F.map ((SingleHomology.zeroData N n).homologyIso.hom ≫ (singleObjXSelf (.up ℕ) n N).hom) :=
        congrArg (fun z => ((K.sc n).mapHomologyIso F).hom ≫ F.map z)
          (SingleHomology.zeroData_coordinate N n).symm
      _ = (((K.sc n).mapHomologyIso F).hom ≫ F.map (SingleHomology.zeroData N n).homologyIso.hom) ≫
          F.map (singleObjXSelf (.up ℕ) n N).hom := by rw [F.map_comp, Category.assoc]
      _ = _ := congrArg (fun z => z ≫ F.map (singleObjXSelf (.up ℕ) n N).hom)
        (SingleLeftHomology.homologyIso F (K.sc n) (SingleHomology.zeroData N n))
  apply Eq.trans ?_ he.symm
  apply (cancel_epi (L.homologyπ n)).mp
  have hc : ((SingleHomology.zeroData N n).map F).cyclesIso.hom =
      ((((HomologicalComplex.single C (.up ℕ) n).obj N).sc n).map F).iCycles := by
    have h := ((SingleHomology.zeroData N n).map F).cyclesIso_hom_comp_i
    change ((SingleHomology.zeroData N n).map F).cyclesIso.hom ≫ F.map (𝟙 _) = _ at h
    erw [F.map_id, Category.comp_id] at h
    exact h
  have hπ : L.homologyπ n ≫ ((SingleHomology.zeroData N n).map F).homologyIso.hom = L.iCycles n := by
    have h := ((SingleHomology.zeroData N n).map F).homologyπ_comp_homologyIso_hom
    change L.homologyπ n ≫ ((SingleHomology.zeroData N n).map F).homologyIso.hom =
      ((SingleHomology.zeroData N n).map F).cyclesIso.hom ≫ F.map (𝟙 _) at h
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

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.SingleLeftHomology
