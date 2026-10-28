import OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentrationSingle

/-! # Concentration Single -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationSingle

noncomputable section

/-! The canonical concentration zigzag, after any functor inverting
its original maps, is normalized on every genuine map to a single. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] (F : CochainComplex C ℕ ⥤ D)
  (K : CochainComplex C ℕ) (c : ℕ)
  [IsIso (F.map (CohomologyConcentration.projection K c))] [IsIso (F.map (CohomologyConcentration.inclusion K c))]

def iso : F.obj K ≅ F.obj ((single C (.up ℕ) c).obj (K.homology c)) :=
  asIso (F.map (CohomologyConcentration.projection K c)) ≪≫ (asIso (F.map (CohomologyConcentration.inclusion K c))).symm

variable (N : C) (a : K ⟶ (single C (.up ℕ) c).obj N)
  [IsIso (F.map (CohomologyConcentration.projection ((single C (.up ℕ) c).obj N) c))]

theorem map_to_single : F.map a = (iso F K c).hom ≫
    F.map ((single C (.up ℕ) c).map
      (homologyMap a c ≫ (singleObjHomologySelfIso (.up ℕ) c N).hom)) := by
  let L := (single C (.up ℕ) c).obj N
  let b := (single C (.up ℕ) c).map
    (homologyMap a c ≫ (singleObjHomologySelfIso (.up ℕ) c N).hom)
  have hb : b ≫ CohomologyConcentration.projection L c = CohomologyConcentration.inclusion K c ≫ truncGEMap a (CohomologyConcentration.shift c) := by
    dsimp only [b]
    rw [Functor.map_comp, Category.assoc,
      ← CohomologyConcentrationSingle.inclusion_single c N]
    exact CohomologyConcentrationNaturality.inclusion_naturality a c
  have hπ : a ≫ CohomologyConcentration.projection L c = CohomologyConcentration.projection K c ≫ truncGEMap a (CohomologyConcentration.shift c) :=
    (πTruncGE_naturality a (CohomologyConcentration.shift c)).symm
  have hb' : F.map b ≫ F.map (CohomologyConcentration.projection L c) =
      F.map (CohomologyConcentration.inclusion K c) ≫ F.map (truncGEMap a (CohomologyConcentration.shift c)) := by
    rw [← F.map_comp, hb, F.map_comp]
  have hπ' : F.map a ≫ F.map (CohomologyConcentration.projection L c) =
      F.map (CohomologyConcentration.projection K c) ≫ F.map (truncGEMap a (CohomologyConcentration.shift c)) := by
    rw [← F.map_comp, hπ, F.map_comp]
  apply (cancel_mono (F.map (CohomologyConcentration.projection L c))).mp
  change F.map a ≫ F.map (CohomologyConcentration.projection L c) =
    (((asIso (F.map (CohomologyConcentration.projection K c))).hom ≫
      (asIso (F.map (CohomologyConcentration.inclusion K c))).inv) ≫ F.map b) ≫ F.map (CohomologyConcentration.projection L c)
  simp only [Category.assoc]
  rw [hπ', hb']
  change F.map (CohomologyConcentration.projection K c) ≫ F.map (truncGEMap a (CohomologyConcentration.shift c)) =
    F.map (CohomologyConcentration.projection K c) ≫ (asIso (F.map (CohomologyConcentration.inclusion K c))).inv ≫
      (asIso (F.map (CohomologyConcentration.inclusion K c))).hom ≫ F.map (truncGEMap a (CohomologyConcentration.shift c))
  rw [Iso.inv_hom_id_assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationSingle
