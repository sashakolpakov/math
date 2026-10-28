import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationMap

/-! # Concentration Zigzag Single -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentrationZigzagSingle

noncomputable section

/-! A normalized concentration zigzag gives the actual image of every
map to a single complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.ConcentrationSingle
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] (G : CochainComplex C ℕ ⥤ D)
  (K S T : CochainComplex C ℕ) (c : ℕ)
  (p : K ⟶ T) (i : S ⟶ T) (N : C)
  (s : S ⟶ (single C (.up ℕ) c).obj N) (e : K.homology c ≅ N)
  [QuasiIsoAt p c] [IsIso (G.map i)]
  [IsIso (G.map (CohomologyConcentration.projection K c))] [IsIso (G.map (CohomologyConcentration.inclusion K c))]
  [IsIso (G.map (CohomologyConcentration.projection S c))] [IsIso (G.map (CohomologyConcentration.inclusion S c))]
  [IsIso (G.map (CohomologyConcentration.projection T c))] [IsIso (G.map (CohomologyConcentration.inclusion T c))]
  [IsIso (G.map (CohomologyConcentration.projection ((single C (.up ℕ) c).obj N) c))]

theorem map_to_single
    (h : homologyMap i c = homologyMap s c ≫
      (singleObjHomologySelfIso (.up ℕ) c N).hom ≫ e.inv ≫ homologyMap p c)
    (M : C) (a : K ⟶ (single C (.up ℕ) c).obj M)
    [IsIso (G.map (CohomologyConcentration.projection ((single C (.up ℕ) c).obj M) c))] :
    G.map a = (G.map p ≫ (asIso (G.map i)).inv) ≫ G.map s ≫
      G.map ((single C (.up ℕ) c).map
        (e.inv ≫ homologyMap a c ≫ (singleObjHomologySelfIso (.up ℕ) c M).hom)) := by
  have hp := IntegralComparison.Functor.ConcentrationMap.naturality G p c
  have hi := IntegralComparison.Functor.ConcentrationMap.naturality G i c
  have hs := IntegralComparison.Functor.ConcentrationSingle.map_to_single G S c N s
  have hI : G.map i ≫ (IntegralComparison.Functor.ConcentrationSingle.iso G T c).hom =
      G.map s ≫ G.map ((single C (.up ℕ) c).map e.inv) ≫
        G.map ((single C (.up ℕ) c).map (homologyMap p c)) := by
    calc
      _ = (IntegralComparison.Functor.ConcentrationSingle.iso G S c).hom ≫ G.map ((single C (.up ℕ) c).map (homologyMap i c)) := hi
      _ = ((IntegralComparison.Functor.ConcentrationSingle.iso G S c).hom ≫ G.map ((single C (.up ℕ) c).map
          (homologyMap s c ≫ (singleObjHomologySelfIso (.up ℕ) c N).hom))) ≫
            G.map ((single C (.up ℕ) c).map e.inv) ≫
              G.map ((single C (.up ℕ) c).map (homologyMap p c)) := by
        rw [h]
        simp only [Functor.map_comp, Category.assoc]
      _ = _ := by rw [← hs]
  have hK : (IntegralComparison.Functor.ConcentrationSingle.iso G K c).hom =
      (G.map p ≫ (asIso (G.map i)).inv) ≫ G.map s ≫
        G.map ((single C (.up ℕ) c).map e.inv) := by
    apply (cancel_mono (G.map ((single C (.up ℕ) c).map (homologyMap p c)))).mp
    simp only [Category.assoc]
    rw [← hp, ← hI]
    change G.map p ≫ (IntegralComparison.Functor.ConcentrationSingle.iso G T c).hom =
      G.map p ≫ (asIso (G.map i)).inv ≫ (asIso (G.map i)).hom ≫ (IntegralComparison.Functor.ConcentrationSingle.iso G T c).hom
    rw [Iso.inv_hom_id_assoc]
  rw [IntegralComparison.Functor.ConcentrationSingle.map_to_single G K c M a, hK]
  simp only [Functor.map_comp, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentrationZigzagSingle
