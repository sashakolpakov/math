import OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality

/-! # Cohomology Concentration Single -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationSingle

noncomputable section

/-! The canonical concentration zigzag has its literal normalization
on a single complex. This determines its compatibility with genuine
maps to a single surviving coefficient object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration

theorem inclusion_component (K : CochainComplex C ℕ) (c : ℕ) :
    (CohomologyConcentration.inclusion K c).f c =
      (singleObjXSelf (.up ℕ) c (K.homology c)).hom ≫
        (CohomologyConcentration.cyclesHomologyIso K c).inv ≫ (CohomologyConcentration.tail K c).iCycles 0 ≫
          ((CohomologyConcentration.tail K c).extendXIso (CohomologyConcentration.shift c) (show (CohomologyConcentration.shift c).f 0 = c by simp [CohomologyConcentration.shift])).inv := by
  simp only [CohomologyConcentration.inclusion, HomologicalComplex.comp_f, single_map_f_self,
    extendSingleIso_inv_f, extendMap_f _ (CohomologyConcentration.shift c) (show (CohomologyConcentration.shift c).f 0 = c by simp [CohomologyConcentration.shift]),
    CohomologyConcentration.zeroCyclesMap_f_zero, Category.assoc, Iso.inv_hom_id_assoc]
  have h0 : (singleObjXSelf (.up ℕ) 0 ((CohomologyConcentration.tail K c).cycles 0)).inv = 𝟙 _ := rfl
  rw [h0, Category.id_comp]

theorem cycles_normalization (K : CochainComplex C ℕ) (c : ℕ) :
    K.homologyπ c ≫ (CohomologyConcentration.cyclesHomologyIso K c).inv =
      cyclesMap (CohomologyConcentration.projection K c) c ≫
        ((CohomologyConcentration.tail K c).extendCyclesIso (CohomologyConcentration.shift c)
          (show (CohomologyConcentration.shift c).f 0 = c by simp [CohomologyConcentration.shift])).hom := by
  dsimp only [CohomologyConcentration.cyclesHomologyIso, Iso.trans_inv, Iso.symm_inv]
  erw [isoOfQuasiIsoAt_hom]
  simp only [Category.assoc]
  erw [homologyπ_naturality_assoc, homologyπ_extendHomologyIso_hom_assoc]
  have hπ := (CohomologyConcentration.tail K c).isoHomologyπ₀.hom_inv_id
  change (CohomologyConcentration.tail K c).homologyπ 0 ≫ (CohomologyConcentration.tail K c).isoHomologyπ₀.inv = 𝟙 _ at hπ
  rw [hπ, Category.comp_id]

theorem inclusion_single (c : ℕ) (N : C) :
    CohomologyConcentration.inclusion ((single C (.up ℕ) c).obj N) c =
      (single C (.up ℕ) c).map (singleObjHomologySelfIso (.up ℕ) c N).hom ≫
        CohomologyConcentration.projection ((single C (.up ℕ) c).obj N) c := by
  let K := (single C (.up ℕ) c).obj N
  change CohomologyConcentration.inclusion K c =
    (single C (.up ℕ) c).map (singleObjHomologySelfIso (.up ℕ) c N).hom ≫ CohomologyConcentration.projection K c
  apply HomologicalComplex.from_single_hom_ext
  rw [inclusion_component, HomologicalComplex.comp_f, single_map_f_self]
  apply (cancel_epi (singleObjXSelf (.up ℕ) c (K.homology c)).inv).mp
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  apply (cancel_epi (K.homologyπ c)).mp
  erw [← Category.assoc (K.homologyπ c) (CohomologyConcentration.cyclesHomologyIso K c).inv,
    cycles_normalization]
  simp only [Category.assoc]
  erw [homologyπ_singleObjHomologySelfIso_hom_assoc, singleObjCyclesSelfIso_hom]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_assoc, extendCyclesIso_hom_iCycles_assoc,
    Iso.hom_inv_id, Category.comp_id, cyclesMap_i]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationSingle
