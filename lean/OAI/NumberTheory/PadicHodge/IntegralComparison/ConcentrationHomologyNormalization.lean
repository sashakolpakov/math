import OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationSingle

/-! # Concentration Homology Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentrationHomologyNormalization

noncomputable section

/-! The original concentration inclusion induces the canonical
identity on its surviving cohomology object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : CochainComplex C ℕ) (c : ℕ)
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationSingle

theorem cycles : K.homologyπ c ≫
    (singleObjCyclesSelfIso (.up ℕ) c (K.homology c)).inv ≫
      cyclesMap (CohomologyConcentration.inclusion K c) c = cyclesMap (CohomologyConcentration.projection K c) c := by
  apply (cancel_mono ((CohomologyConcentration.truncation K c).iCycles c)).mp
  simp only [Category.assoc]
  rw [cyclesMap_i (CohomologyConcentration.inclusion K c) c, singleObjCyclesSelfIso_inv_iCycles_assoc,
    CohomologyConcentrationSingle.inclusion_component]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc (K.homologyπ c) (CohomologyConcentration.cyclesHomologyIso K c).inv,
    CohomologyConcentrationSingle.cycles_normalization]
  simp only [Category.assoc]
  rw [extendCyclesIso_hom_iCycles_assoc]
  simp only [Iso.hom_inv_id, Category.comp_id]
  rfl

theorem inclusion : homologyMap (CohomologyConcentration.inclusion K c) c =
    (singleObjHomologySelfIso (.up ℕ) c (K.homology c)).hom ≫
      homologyMap (CohomologyConcentration.projection K c) c := by
  apply (cancel_epi (singleObjHomologySelfIso (.up ℕ) c (K.homology c)).inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply (cancel_epi (K.homologyπ c)).mp
  rw [← singleObjCyclesSelfIso_inv_homologyπ]
  simp only [Category.assoc]
  rw [homologyπ_naturality (CohomologyConcentration.inclusion K c) c,
    homologyπ_naturality (CohomologyConcentration.projection K c) c]
  simpa only [Category.assoc] using congrArg
    (fun a => a ≫ (CohomologyConcentration.truncation K c).homologyπ c) (cycles K c)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentrationHomologyNormalization
