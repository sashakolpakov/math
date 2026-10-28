import OAI.RepresentationTheory.Hecke.RadialDilation.FunctionSumMap
import OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex

/-! # Indexed Phase Functions -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPhaseFunctions.Realization

/-! Pure function identities for relabeled local phase coordinates. -/

theorem function_reindex_map_sum {I J R S : Type*} [TopologicalSpace S]
    (e : I ≃ J) (F : R → S) (p s : I → R) :
    PositionReindex.Realization.positionReindex (e.sumCongr e) (fun i => F (Sum.elim p s i)) =
      Sum.elim (fun j => F (p (e.symm j))) (fun j => F (s (e.symm j))) :=
  (congrArg (PositionReindex.Realization.positionReindex (e.sumCongr e)) (FunctionSumMap.Realization.function_map_sum_elim F p s)).trans
    (PositionReindex.Realization.positionReindex_sum_elim e (fun i => F (p i)) (fun i => F (s i)))

theorem function_reindex_map_swap_sum {I J R S : Type*} [TopologicalSpace S]
    (e : I ≃ J) (F : R → S) (p s : I → R) :
    SymplecticSwap.Realization.swapPhase (PositionReindex.Realization.positionReindex (e.sumCongr e) (fun i => F (Sum.elim p s i))) =
      Sum.elim (fun j => F (s (e.symm j))) (fun j => F (p (e.symm j))) :=
  (congrArg SymplecticSwap.Realization.swapPhase (function_reindex_map_sum e F p s)).trans
    (FunctionSumMap.Realization.function_map_swap_sum_elim id (fun j => F (p (e.symm j))) (fun j => F (s (e.symm j))))

theorem function_reindex_phase_components {I J R S : Type*} [TopologicalSpace S]
    (e : I ≃ J) (F : R → S) (x : Sum I I → R) :
    Sum.elim (fun j => F (x (Sum.inr (e.symm j)))) (fun j => F (x (Sum.inl (e.symm j)))) =
      SymplecticSwap.Realization.swapPhase (PositionReindex.Realization.positionReindex (e.sumCongr e) (fun i => F (x i))) := by
  funext i
  cases i <;> rfl

end OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPhaseFunctions.Realization
