import OAI.NumberTheory.PadicHodge.IntegralComparison.LeftExactHomology

/-! # Homology Compose -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyCompose.Comparison

noncomputable section

/-! Compatibility of the actual left exact homology comparison with composition. -/

open _root_.CategoryTheory Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.LeftExactHomology.Comparison

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteLimits G] (S : ShortComplex C)

local instance : PreservesFiniteLimits (F ⋙ G) where
  preservesFiniteLimits J _ _ := by infer_instance

theorem cycles : (LeftExactHomology.Comparison.cyclesIso (F ⋙ G) S).hom =
    (LeftExactHomology.Comparison.cyclesIso G (S.map F)).hom ≫ G.map (LeftExactHomology.Comparison.cyclesIso F S).hom := by
  apply (cancel_mono (G.map (F.map S.iCycles))).mp
  have hl := LeftExactHomology.Comparison.cycles_i (F ⋙ G) S
  have hr : ((LeftExactHomology.Comparison.cyclesIso G (S.map F)).hom ≫ G.map (LeftExactHomology.Comparison.cyclesIso F S).hom) ≫ G.map (F.map S.iCycles) =
      ((S.map F).map G).iCycles := by
    rw [Category.assoc, ← G.map_comp, LeftExactHomology.Comparison.cycles_i]
    exact LeftExactHomology.Comparison.cycles_i G (S.map F)
  exact hl.trans hr.symm

theorem homology : LeftExactHomology.Comparison.map (F ⋙ G) S = LeftExactHomology.Comparison.map G (S.map F) ≫ G.map (LeftExactHomology.Comparison.map F S) := by
  apply (cancel_epi ((S.map F).map G).homologyπ).mp
  have hl : ((S.map F).map G).homologyπ ≫ LeftExactHomology.Comparison.map (F ⋙ G) S =
      ((LeftExactHomology.Comparison.cyclesIso G (S.map F)).hom ≫ G.map (LeftExactHomology.Comparison.cyclesIso F S).hom) ≫ G.map (F.map S.homologyπ) :=
    (LeftExactHomology.Comparison.π_map (F ⋙ G) S).trans
      (congrArg (fun a => a ≫ G.map (F.map S.homologyπ)) (cycles F G S))
  have hr : ((S.map F).map G).homologyπ ≫ (LeftExactHomology.Comparison.map G (S.map F) ≫ G.map (LeftExactHomology.Comparison.map F S)) =
      ((LeftExactHomology.Comparison.cyclesIso G (S.map F)).hom ≫ G.map (LeftExactHomology.Comparison.cyclesIso F S).hom) ≫ G.map (F.map S.homologyπ) := by
    rw [← Category.assoc, LeftExactHomology.Comparison.π_map, Category.assoc, ← G.map_comp, LeftExactHomology.Comparison.π_map, G.map_comp, ← Category.assoc]
  exact hl.trans hr.symm

theorem isIso_map [PreservesFiniteColimits G] [(F ⋙ G).PreservesLeftHomologyOf S] :
    IsIso (G.map (LeftExactHomology.Comparison.map F S)) := by
  have : IsIso (LeftExactHomology.Comparison.map G (S.map F)) := LeftExactHomology.Comparison.isIso G (S.map F)
  have : IsIso (LeftExactHomology.Comparison.map G (S.map F) ≫ G.map (LeftExactHomology.Comparison.map F S)) :=
    (homology F G S) ▸ LeftExactHomology.Comparison.isIso (F ⋙ G) S
  exact IsIso.of_isIso_comp_left (LeftExactHomology.Comparison.map G (S.map F)) (G.map (LeftExactHomology.Comparison.map F S))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyCompose.Comparison
