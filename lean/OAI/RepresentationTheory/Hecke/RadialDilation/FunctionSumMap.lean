import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticSwap

/-! # Function Sum Map -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FunctionSumMap.Realization

/-! Coordinatewise maps commute with assembling two families of coordinates. -/

theorem function_map_sum_elim {A B R S : Type*} (F : R → S) (p : A → R) (s : B → R) :
    (fun i => F (Sum.elim p s i)) = Sum.elim (fun i => F (p i)) (fun i => F (s i)) := by
  funext i
  cases i <;> rfl

theorem function_map_swap_sum_elim {I R S : Type*} (F : R → S) (p s : I → R) :
    SymplecticSwap.Realization.swapPhase (fun i => F (Sum.elim p s i)) =
      Sum.elim (fun i => F (s i)) (fun i => F (p i)) := by
  funext i
  cases i <;> rfl

end OAI.RepresentationTheory.Hecke.RadialDilation.FunctionSumMap.Realization
